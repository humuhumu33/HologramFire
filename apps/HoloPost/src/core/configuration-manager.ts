/**
 * Production Configuration Management System
 * 
 * This module provides comprehensive configuration management for the Hologram system,
 * including environment-based configuration, validation, hot-reloading, and secure
 * secret management.
 */

import { EventEmitter } from 'events';
import { readFileSync, watchFile, unwatchFile } from 'node:fs';
import { createHash } from 'node:crypto';
import { z } from 'zod';

export interface ConfigurationSchema {
  [key: string]: z.ZodTypeAny;
}

export interface ConfigurationSource {
  name: string;
  type: 'file' | 'environment' | 'remote' | 'default';
  priority: number;
  data: Record<string, any>;
  lastUpdated: number;
  checksum: string;
}

export interface ConfigurationValidationResult {
  isValid: boolean;
  errors: Array<{
    path: string;
    message: string;
    received: any;
    expected: string;
  }>;
  warnings: Array<{
    path: string;
    message: string;
  }>;
}

export interface ConfigurationChangeEvent {
  source: string;
  changes: Array<{
    path: string;
    oldValue: any;
    newValue: any;
  }>;
  timestamp: number;
}

export class ConfigurationManager extends EventEmitter {
  private schema: ConfigurationSchema;
  private sources: Map<string, ConfigurationSource> = new Map();
  private mergedConfig: Record<string, any> = {};
  private watchers: Map<string, NodeJS.Timeout> = new Map();
  private validationCache: Map<string, ConfigurationValidationResult> = new Map();
  private config: ConfigurationManagerConfig;

  constructor(
    schema: ConfigurationSchema,
    config: Partial<ConfigurationManagerConfig> = {}
  ) {
    super();
    
    this.schema = schema;
    this.config = {
      enableHotReload: true,
      enableValidation: true,
      enableCaching: true,
      cacheTTL: 300000, // 5 minutes
      watchInterval: 1000,
      enableSecrets: true,
      secretsProvider: 'environment',
      enableRemoteConfig: false,
      remoteConfigEndpoint: '',
      remoteConfigInterval: 60000,
      ...config,
    };
    
    this.initializeDefaultSources();
  }

  /**
   * Load configuration from all sources
   */
  async loadConfiguration(): Promise<Record<string, any>> {
    try {
      // Load from all sources in priority order
      const sortedSources = Array.from(this.sources.values())
        .sort((a, b) => a.priority - b.priority);
      
      for (const source of sortedSources) {
        await this.loadFromSource(source);
      }
      
      // Merge configurations
      this.mergeConfigurations();
      
      // Validate merged configuration
      if (this.config.enableValidation) {
        const validation = await this.validateConfiguration(this.mergedConfig);
        if (!validation.isValid) {
          this.emit('validationError', validation);
          throw new Error(`Configuration validation failed: ${validation.errors.map(e => e.message).join(', ')}`);
        }
      }
      
      this.emit('configurationLoaded', this.mergedConfig);
      return this.mergedConfig;
      
    } catch (error) {
      this.emit('error', { operation: 'loadConfiguration', error });
      throw error;
    }
  }

  /**
   * Get configuration value by path
   */
  get<T = any>(path: string, defaultValue?: T): T {
    const keys = path.split('.');
    let value: any = this.mergedConfig;
    
    for (const key of keys) {
      if (value && typeof value === 'object' && key in value) {
        value = value[key];
      } else {
        return defaultValue as T;
      }
    }
    
    return value as T;
  }

  /**
   * Set configuration value by path
   */
  set(path: string, value: any): void {
    const keys = path.split('.');
    let current: any = this.mergedConfig;
    
    for (let i = 0; i < keys.length - 1; i++) {
      const key = keys[i];
      if (!(key in current) || typeof current[key] !== 'object') {
        current[key] = {};
      }
      current = current[key];
    }
    
    const lastKey = keys[keys.length - 1];
    const oldValue = current[lastKey];
    current[lastKey] = value;
    
    this.emit('configurationChanged', {
      path,
      oldValue,
      newValue: value,
      timestamp: Date.now(),
    });
  }

  /**
   * Add configuration source
   */
  addSource(
    name: string,
    type: ConfigurationSource['type'],
    data: Record<string, any>,
    priority: number = 100
  ): void {
    const source: ConfigurationSource = {
      name,
      type,
      priority,
      data,
      lastUpdated: Date.now(),
      checksum: this.calculateChecksum(data),
    };
    
    this.sources.set(name, source);
    
    if (this.config.enableHotReload && type === 'file') {
      this.watchFileSource(name, data);
    }
    
    this.emit('sourceAdded', { name, type, priority });
  }

  /**
   * Remove configuration source
   */
  removeSource(name: string): void {
    const source = this.sources.get(name);
    if (source) {
      this.sources.delete(name);
      
      if (this.watchers.has(name)) {
        const watcher = this.watchers.get(name);
        if (watcher) {
          clearInterval(watcher);
        }
        this.watchers.delete(name);
      }
      
      this.emit('sourceRemoved', { name, type: source.type });
    }
  }

  /**
   * Validate configuration against schema
   */
  async validateConfiguration(config: Record<string, any>): Promise<ConfigurationValidationResult> {
    const cacheKey = this.calculateChecksum(config);
    
    if (this.config.enableCaching && this.validationCache.has(cacheKey)) {
      return this.validationCache.get(cacheKey)!;
    }
    
    const errors: ConfigurationValidationResult['errors'] = [];
    const warnings: ConfigurationValidationResult['warnings'] = [];
    
    try {
      // Validate using Zod schema
      const result = this.validateWithSchema(config);
      
      if (!result.success) {
        for (const issue of result.error.issues) {
          errors.push({
            path: issue.path.join('.'),
            message: issue.message,
            received: issue.input,
            expected: issue.expected || 'unknown',
          });
        }
      }
      
      // Additional custom validation
      this.performCustomValidation(config, errors, warnings);
      
    } catch (error) {
      errors.push({
        path: 'root',
        message: `Validation error: ${error.message}`,
        received: config,
        expected: 'valid configuration',
      });
    }
    
    const validationResult: ConfigurationValidationResult = {
      isValid: errors.length === 0,
      errors,
      warnings,
    };
    
    if (this.config.enableCaching) {
      this.validationCache.set(cacheKey, validationResult);
    }
    
    return validationResult;
  }

  /**
   * Get configuration sources
   */
  getSources(): ConfigurationSource[] {
    return Array.from(this.sources.values());
  }

  /**
   * Get configuration metadata
   */
  getMetadata(): {
    sources: ConfigurationSource[];
    lastLoaded: number;
    validationCacheSize: number;
    watchersActive: number;
  } {
    return {
      sources: this.getSources(),
      lastLoaded: Date.now(),
      validationCacheSize: this.validationCache.size,
      watchersActive: this.watchers.size,
    };
  }

  /**
   * Clear configuration cache
   */
  clearCache(): void {
    this.validationCache.clear();
    this.emit('cacheCleared');
  }

  /**
   * Stop configuration manager
   */
  stop(): void {
    // Clear all watchers
    for (const [name, watcher] of this.watchers) {
      clearInterval(watcher);
    }
    this.watchers.clear();
    
    this.emit('stopped');
  }

  // Private helper methods

  private initializeDefaultSources(): void {
    // Add environment variables source
    this.addSource('environment', 'environment', process.env, 10);
    
    // Add default configuration source
    this.addSource('defaults', 'default', this.getDefaultConfiguration(), 1000);
  }

  private async loadFromSource(source: ConfigurationSource): Promise<void> {
    try {
      switch (source.type) {
        case 'file':
          await this.loadFromFile(source);
          break;
        case 'environment':
          this.loadFromEnvironment(source);
          break;
        case 'remote':
          await this.loadFromRemote(source);
          break;
        case 'default':
          // Default source is already loaded
          break;
      }
    } catch (error) {
      this.emit('sourceLoadError', { source: source.name, error });
    }
  }

  private async loadFromFile(source: ConfigurationSource): Promise<void> {
    try {
      const filePath = source.data.path;
      if (!filePath) {
        throw new Error('File path not specified');
      }
      
      const fileContent = readFileSync(filePath, 'utf8');
      const configData = JSON.parse(fileContent);
      
      source.data = configData;
      source.lastUpdated = Date.now();
      source.checksum = this.calculateChecksum(configData);
      
      this.emit('fileLoaded', { source: source.name, filePath });
    } catch (error) {
      throw new Error(`Failed to load file source ${source.name}: ${error.message}`);
    }
  }

  private loadFromEnvironment(source: ConfigurationSource): void {
    const envConfig: Record<string, any> = {};
    
    for (const [key, value] of Object.entries(process.env)) {
      if (key.startsWith('HOLOGRAM_')) {
        const configKey = key.replace('HOLOGRAM_', '').toLowerCase().replace(/_/g, '.');
        envConfig[configKey] = this.parseEnvironmentValue(value);
      }
    }
    
    source.data = envConfig;
    source.lastUpdated = Date.now();
    source.checksum = this.calculateChecksum(envConfig);
  }

  private async loadFromRemote(source: ConfigurationSource): Promise<void> {
    if (!this.config.enableRemoteConfig) {
      return;
    }
    
    try {
      // In a real implementation, this would fetch from a remote configuration service
      // For now, we'll simulate remote loading
      const remoteConfig = await this.fetchRemoteConfiguration();
      
      source.data = remoteConfig;
      source.lastUpdated = Date.now();
      source.checksum = this.calculateChecksum(remoteConfig);
      
      this.emit('remoteLoaded', { source: source.name });
    } catch (error) {
      throw new Error(`Failed to load remote source ${source.name}: ${error.message}`);
    }
  }

  private mergeConfigurations(): void {
    const sortedSources = Array.from(this.sources.values())
      .sort((a, b) => a.priority - b.priority);
    
    this.mergedConfig = {};
    
    for (const source of sortedSources) {
      this.mergedConfig = this.deepMerge(this.mergedConfig, source.data);
    }
  }

  private deepMerge(target: any, source: any): any {
    const result = { ...target };
    
    for (const key in source) {
      if (source[key] && typeof source[key] === 'object' && !Array.isArray(source[key])) {
        result[key] = this.deepMerge(result[key] || {}, source[key]);
      } else {
        result[key] = source[key];
      }
    }
    
    return result;
  }

  private watchFileSource(name: string, data: Record<string, any>): void {
    const filePath = data.path;
    if (!filePath) {
      return;
    }
    
    const watcher = setInterval(() => {
      try {
        const fileContent = readFileSync(filePath, 'utf8');
        const newData = JSON.parse(fileContent);
        const newChecksum = this.calculateChecksum(newData);
        
        const source = this.sources.get(name);
        if (source && source.checksum !== newChecksum) {
          const oldData = source.data;
          source.data = newData;
          source.lastUpdated = Date.now();
          source.checksum = newChecksum;
          
          this.mergeConfigurations();
          
          this.emit('sourceUpdated', {
            name,
            oldData,
            newData,
            timestamp: Date.now(),
          });
        }
      } catch (error) {
        this.emit('watchError', { name, error });
      }
    }, this.config.watchInterval);
    
    this.watchers.set(name, watcher);
  }

  private validateWithSchema(config: Record<string, any>): { success: boolean; error?: any } {
    try {
      // Create a Zod object schema from the configuration schema
      const zodSchema = z.object(this.schema);
      zodSchema.parse(config);
      return { success: true };
    } catch (error) {
      return { success: false, error };
    }
  }

  private performCustomValidation(
    config: Record<string, any>,
    errors: ConfigurationValidationResult['errors'],
    warnings: ConfigurationValidationResult['warnings']
  ): void {
    // Custom validation logic
    if (config.performance?.targetThroughput && config.performance.targetThroughput > 100) {
      warnings.push({
        path: 'performance.targetThroughput',
        message: 'Target throughput is very high, ensure adequate hardware resources',
      });
    }
    
    if (config.network?.lanes && config.network.lanes > 1000) {
      warnings.push({
        path: 'network.lanes',
        message: 'High number of network lanes may impact performance',
      });
    }
  }

  private parseEnvironmentValue(value: string | undefined): any {
    if (!value) {
      return undefined;
    }
    
    // Try to parse as JSON
    try {
      return JSON.parse(value);
    } catch {
      // Return as string
      return value;
    }
  }

  private calculateChecksum(data: any): string {
    const str = JSON.stringify(data);
    return createHash('sha256').update(str).digest('hex');
  }

  private getDefaultConfiguration(): Record<string, any> {
    return {
      performance: {
        targetThroughput: 25, // GB/s
        maxWorkers: 128,
        networkLanes: 512,
        hardwareAcceleration: true,
        compressionEnabled: true,
      },
      network: {
        timeout: 30000,
        retries: 3,
        keepAlive: true,
        compression: true,
      },
      storage: {
        enableCaching: true,
        cacheSize: 10000,
        cacheTTL: 3600000,
      },
      monitoring: {
        enabled: true,
        interval: 1000,
        enableAlerts: true,
      },
      security: {
        enableEncryption: true,
        enableAuthentication: true,
        enableAuthorization: true,
      },
    };
  }

  private async fetchRemoteConfiguration(): Promise<Record<string, any>> {
    // Simulate remote configuration fetch
    return {
      remote: {
        enabled: true,
        lastFetched: Date.now(),
      },
    };
  }
}

export interface ConfigurationManagerConfig {
  enableHotReload: boolean;
  enableValidation: boolean;
  enableCaching: boolean;
  cacheTTL: number;
  watchInterval: number;
  enableSecrets: boolean;
  secretsProvider: 'environment' | 'vault' | 'file';
  enableRemoteConfig: boolean;
  remoteConfigEndpoint: string;
  remoteConfigInterval: number;
}

// Predefined configuration schemas
export const hologramConfigSchema: ConfigurationSchema = {
  performance: z.object({
    targetThroughput: z.number().min(1).max(1000),
    maxWorkers: z.number().min(1).max(1000),
    networkLanes: z.number().min(1).max(10000),
    hardwareAcceleration: z.boolean(),
    compressionEnabled: z.boolean(),
  }),
  network: z.object({
    timeout: z.number().min(1000).max(300000),
    retries: z.number().min(0).max(10),
    keepAlive: z.boolean(),
    compression: z.boolean(),
  }),
  storage: z.object({
    enableCaching: z.boolean(),
    cacheSize: z.number().min(100).max(1000000),
    cacheTTL: z.number().min(60000).max(86400000),
  }),
  monitoring: z.object({
    enabled: z.boolean(),
    interval: z.number().min(100).max(60000),
    enableAlerts: z.boolean(),
  }),
  security: z.object({
    enableEncryption: z.boolean(),
    enableAuthentication: z.boolean(),
    enableAuthorization: z.boolean(),
  }),
};

// Export default configuration
export const defaultConfigManagerConfig: ConfigurationManagerConfig = {
  enableHotReload: true,
  enableValidation: true,
  enableCaching: true,
  cacheTTL: 300000,
  watchInterval: 1000,
  enableSecrets: true,
  secretsProvider: 'environment',
  enableRemoteConfig: false,
  remoteConfigEndpoint: '',
  remoteConfigInterval: 60000,
};
