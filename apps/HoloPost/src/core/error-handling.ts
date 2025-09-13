/**
 * Comprehensive Error Handling System
 * 
 * This module provides production-ready error handling, logging, and recovery
 * mechanisms for the Hologram system, including structured error types,
 * automatic retry logic, and comprehensive error reporting.
 */

import { EventEmitter } from 'events';
import { createHash } from 'node:crypto';

export interface ErrorContext {
  operation: string;
  component: string;
  userId?: string;
  sessionId?: string;
  requestId?: string;
  timestamp: number;
  metadata: Record<string, any>;
}

export interface ErrorMetrics {
  totalErrors: number;
  errorsByType: Map<string, number>;
  errorsByComponent: Map<string, number>;
  errorsByOperation: Map<string, number>;
  recentErrors: Array<{
    error: HologramError;
    context: ErrorContext;
    timestamp: number;
  }>;
}

export interface RetryConfig {
  maxRetries: number;
  baseDelay: number;
  maxDelay: number;
  backoffMultiplier: number;
  retryableErrors: string[];
}

export interface ErrorReportingConfig {
  enableReporting: boolean;
  reportEndpoint?: string;
  reportInterval: number;
  maxReportSize: number;
  includeStackTrace: boolean;
  includeUserData: boolean;
}

export class HologramError extends Error {
  public readonly code: string;
  public readonly type: ErrorType;
  public readonly severity: ErrorSeverity;
  public readonly context: ErrorContext;
  public readonly retryable: boolean;
  public readonly timestamp: number;
  public readonly errorId: string;

  constructor(
    message: string,
    type: ErrorType,
    severity: ErrorSeverity = 'medium',
    context: Partial<ErrorContext> = {},
    retryable: boolean = false
  ) {
    super(message);
    this.name = 'HologramError';
    this.code = this.generateErrorCode(type);
    this.type = type;
    this.severity = severity;
    this.context = {
      operation: 'unknown',
      component: 'unknown',
      timestamp: Date.now(),
      metadata: {},
      ...context,
    };
    this.retryable = retryable;
    this.timestamp = Date.now();
    this.errorId = this.generateErrorId();
  }

  private generateErrorCode(type: ErrorType): string {
    const typeMap: Record<ErrorType, string> = {
      'validation': 'VAL',
      'authentication': 'AUTH',
      'authorization': 'AUTHZ',
      'network': 'NET',
      'timeout': 'TIMEOUT',
      'resource': 'RES',
      'configuration': 'CONFIG',
      'internal': 'INT',
      'external': 'EXT',
      'data': 'DATA',
      'performance': 'PERF',
      'security': 'SEC',
      'compatibility': 'COMPAT',
      'rate_limit': 'RATE',
      'quota': 'QUOTA',
    };
    return typeMap[type] || 'UNK';
  }

  private generateErrorId(): string {
    const data = `${this.type}-${this.timestamp}-${Math.random()}`;
    return createHash('sha256').update(data).digest('hex').substring(0, 16);
  }

  toJSON(): any {
    return {
      name: this.name,
      message: this.message,
      code: this.code,
      type: this.type,
      severity: this.severity,
      context: this.context,
      retryable: this.retryable,
      timestamp: this.timestamp,
      errorId: this.errorId,
      stack: this.stack,
    };
  }
}

export type ErrorType = 
  | 'validation'
  | 'authentication'
  | 'authorization'
  | 'network'
  | 'timeout'
  | 'resource'
  | 'configuration'
  | 'internal'
  | 'external'
  | 'data'
  | 'performance'
  | 'security'
  | 'compatibility'
  | 'rate_limit'
  | 'quota';

export type ErrorSeverity = 'low' | 'medium' | 'high' | 'critical';

export class ErrorHandler extends EventEmitter {
  private metrics: ErrorMetrics;
  private retryConfig: RetryConfig;
  private reportingConfig: ErrorReportingConfig;
  private errorBuffer: Array<{ error: HologramError; context: ErrorContext }> = [];
  private reportingTimer: NodeJS.Timeout | null = null;

  constructor(
    retryConfig: Partial<RetryConfig> = {},
    reportingConfig: Partial<ErrorReportingConfig> = {}
  ) {
    super();
    
    this.retryConfig = {
      maxRetries: 3,
      baseDelay: 1000,
      maxDelay: 30000,
      backoffMultiplier: 2,
      retryableErrors: ['network', 'timeout', 'rate_limit'],
      ...retryConfig,
    };
    
    this.reportingConfig = {
      enableReporting: true,
      reportInterval: 60000, // 1 minute
      maxReportSize: 1000,
      includeStackTrace: true,
      includeUserData: false,
      ...reportingConfig,
    };
    
    this.metrics = {
      totalErrors: 0,
      errorsByType: new Map(),
      errorsByComponent: new Map(),
      errorsByOperation: new Map(),
      recentErrors: [],
    };
    
    if (this.reportingConfig.enableReporting) {
      this.startErrorReporting();
    }
  }

  /**
   * Handle an error with automatic retry logic
   */
  async handleError<T>(
    operation: () => Promise<T>,
    context: Partial<ErrorContext> = {},
    customRetryConfig?: Partial<RetryConfig>
  ): Promise<T> {
    const config = { ...this.retryConfig, ...customRetryConfig };
    let lastError: Error | null = null;
    
    for (let attempt = 0; attempt <= config.maxRetries; attempt++) {
      try {
        const result = await operation();
        if (attempt > 0) {
          this.emit('retrySuccess', { attempt, context });
        }
        return result;
      } catch (error) {
        lastError = error;
        
        const hologramError = this.wrapError(error, context);
        this.recordError(hologramError, context);
        
        // Check if error is retryable
        if (attempt < config.maxRetries && this.isRetryableError(hologramError, config)) {
          const delay = this.calculateRetryDelay(attempt, config);
          this.emit('retryAttempt', { attempt, delay, error: hologramError, context });
          await this.sleep(delay);
          continue;
        }
        
        // Error is not retryable or max retries reached
        this.emit('error', hologramError, context);
        throw hologramError;
      }
    }
    
    throw lastError;
  }

  /**
   * Record an error for metrics and reporting
   */
  recordError(error: HologramError, context: Partial<ErrorContext> = {}): void {
    const fullContext: ErrorContext = {
      operation: 'unknown',
      component: 'unknown',
      timestamp: Date.now(),
      metadata: {},
      ...context,
      ...error.context,
    };
    
    // Update metrics
    this.metrics.totalErrors++;
    
    const typeCount = this.metrics.errorsByType.get(error.type) || 0;
    this.metrics.errorsByType.set(error.type, typeCount + 1);
    
    const componentCount = this.metrics.errorsByComponent.get(fullContext.component) || 0;
    this.metrics.errorsByComponent.set(fullContext.component, componentCount + 1);
    
    const operationCount = this.metrics.errorsByOperation.get(fullContext.operation) || 0;
    this.metrics.errorsByOperation.set(fullContext.operation, operationCount + 1);
    
    // Add to recent errors
    this.metrics.recentErrors.push({
      error,
      context: fullContext,
      timestamp: Date.now(),
    });
    
    // Keep only recent errors
    if (this.metrics.recentErrors.length > 1000) {
      this.metrics.recentErrors = this.metrics.recentErrors.slice(-500);
    }
    
    // Add to error buffer for reporting
    this.errorBuffer.push({ error, context: fullContext });
    
    // Emit error event
    this.emit('errorRecorded', { error, context: fullContext });
  }

  /**
   * Wrap a generic error into a HologramError
   */
  wrapError(error: any, context: Partial<ErrorContext> = {}): HologramError {
    if (error instanceof HologramError) {
      return error;
    }
    
    // Determine error type and severity
    const { type, severity, retryable } = this.classifyError(error);
    
    return new HologramError(
      error.message || 'Unknown error occurred',
      type,
      severity,
      context,
      retryable
    );
  }

  /**
   * Get error metrics
   */
  getMetrics(): ErrorMetrics {
    return { ...this.metrics };
  }

  /**
   * Get error statistics
   */
  getErrorStats(): {
    totalErrors: number;
    errorRate: number;
    topErrorTypes: Array<{ type: string; count: number }>;
    topErrorComponents: Array<{ component: string; count: number }>;
    recentErrorRate: number;
  } {
    const now = Date.now();
    const oneHourAgo = now - 3600000;
    const recentErrors = this.metrics.recentErrors.filter(e => e.timestamp > oneHourAgo);
    
    const topErrorTypes = Array.from(this.metrics.errorsByType.entries())
      .map(([type, count]) => ({ type, count }))
      .sort((a, b) => b.count - a.count)
      .slice(0, 10);
    
    const topErrorComponents = Array.from(this.metrics.errorsByComponent.entries())
      .map(([component, count]) => ({ component, count }))
      .sort((a, b) => b.count - a.count)
      .slice(0, 10);
    
    return {
      totalErrors: this.metrics.totalErrors,
      errorRate: this.metrics.totalErrors / (now / 1000 / 3600), // errors per hour
      topErrorTypes,
      topErrorComponents,
      recentErrorRate: recentErrors.length / (3600 / 1000), // recent errors per second
    };
  }

  /**
   * Clear error metrics
   */
  clearMetrics(): void {
    this.metrics = {
      totalErrors: 0,
      errorsByType: new Map(),
      errorsByComponent: new Map(),
      errorsByOperation: new Map(),
      recentErrors: [],
    };
    this.errorBuffer = [];
  }

  /**
   * Stop error reporting
   */
  stop(): void {
    if (this.reportingTimer) {
      clearInterval(this.reportingTimer);
      this.reportingTimer = null;
    }
  }

  // Private helper methods

  private classifyError(error: any): { type: ErrorType; severity: ErrorSeverity; retryable: boolean } {
    const message = error.message?.toLowerCase() || '';
    const name = error.name?.toLowerCase() || '';
    
    // Network errors
    if (message.includes('network') || message.includes('connection') || name.includes('network')) {
      return { type: 'network', severity: 'medium', retryable: true };
    }
    
    // Timeout errors
    if (message.includes('timeout') || name.includes('timeout')) {
      return { type: 'timeout', severity: 'medium', retryable: true };
    }
    
    // Authentication errors
    if (message.includes('auth') || message.includes('unauthorized') || name.includes('auth')) {
      return { type: 'authentication', severity: 'high', retryable: false };
    }
    
    // Validation errors
    if (message.includes('validation') || message.includes('invalid') || name.includes('validation')) {
      return { type: 'validation', severity: 'medium', retryable: false };
    }
    
    // Resource errors
    if (message.includes('resource') || message.includes('not found') || message.includes('404')) {
      return { type: 'resource', severity: 'medium', retryable: false };
    }
    
    // Rate limit errors
    if (message.includes('rate limit') || message.includes('too many requests')) {
      return { type: 'rate_limit', severity: 'medium', retryable: true };
    }
    
    // Default classification
    return { type: 'internal', severity: 'high', retryable: false };
  }

  private isRetryableError(error: HologramError, config: RetryConfig): boolean {
    return error.retryable && config.retryableErrors.includes(error.type);
  }

  private calculateRetryDelay(attempt: number, config: RetryConfig): number {
    const delay = config.baseDelay * Math.pow(config.backoffMultiplier, attempt);
    return Math.min(delay, config.maxDelay);
  }

  private sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  private startErrorReporting(): void {
    this.reportingTimer = setInterval(() => {
      this.reportErrors();
    }, this.reportingConfig.reportInterval);
  }

  private async reportErrors(): Promise<void> {
    if (this.errorBuffer.length === 0) {
      return;
    }
    
    try {
      const errorsToReport = this.errorBuffer.splice(0, this.reportingConfig.maxReportSize);
      
      const report = {
        timestamp: Date.now(),
        errorCount: errorsToReport.length,
        errors: errorsToReport.map(({ error, context }) => ({
          errorId: error.errorId,
          type: error.type,
          severity: error.severity,
          message: error.message,
          context: {
            operation: context.operation,
            component: context.component,
            timestamp: context.timestamp,
          },
          stack: this.reportingConfig.includeStackTrace ? error.stack : undefined,
        })),
      };
      
      this.emit('errorReport', report);
      
      // In a real implementation, this would send the report to an external service
      console.log(`📊 Error report generated: ${errorsToReport.length} errors`);
      
    } catch (error) {
      console.error('Failed to generate error report:', error);
    }
  }
}

// Predefined error types for common scenarios
export class ValidationError extends HologramError {
  constructor(message: string, context: Partial<ErrorContext> = {}) {
    super(message, 'validation', 'medium', context, false);
  }
}

export class AuthenticationError extends HologramError {
  constructor(message: string, context: Partial<ErrorContext> = {}) {
    super(message, 'authentication', 'high', context, false);
  }
}

export class NetworkError extends HologramError {
  constructor(message: string, context: Partial<ErrorContext> = {}) {
    super(message, 'network', 'medium', context, true);
  }
}

export class TimeoutError extends HologramError {
  constructor(message: string, context: Partial<ErrorContext> = {}) {
    super(message, 'timeout', 'medium', context, true);
  }
}

export class ResourceError extends HologramError {
  constructor(message: string, context: Partial<ErrorContext> = {}) {
    super(message, 'resource', 'medium', context, false);
  }
}

export class ConfigurationError extends HologramError {
  constructor(message: string, context: Partial<ErrorContext> = {}) {
    super(message, 'configuration', 'high', context, false);
  }
}

export class PerformanceError extends HologramError {
  constructor(message: string, context: Partial<ErrorContext> = {}) {
    super(message, 'performance', 'medium', context, false);
  }
}

// Export default configurations
export const defaultRetryConfig: RetryConfig = {
  maxRetries: 3,
  baseDelay: 1000,
  maxDelay: 30000,
  backoffMultiplier: 2,
  retryableErrors: ['network', 'timeout', 'rate_limit'],
};

export const defaultReportingConfig: ErrorReportingConfig = {
  enableReporting: true,
  reportInterval: 60000,
  maxReportSize: 1000,
  includeStackTrace: true,
  includeUserData: false,
};
