/**
 * System Primitives for Hologram OS
 * 
 * Implements complete system-level primitives including file systems,
 * network stacks, security contexts, and process management.
 */

import { Atlas12288Encoder } from '../atlas12288/Atlas12288Encoder';
import { WitnessGenerator } from '../witness/WitnessGenerator';
import { CompleteHardwarePrimitives } from '../hardware/complete/HardwarePrimitives';

export interface FileSystem {
  id: string;
  type: 'ext4' | 'xfs' | 'zfs' | 'btrfs' | 'holographic';
  mountpoint: string;
  capacity: number;
  used: number;
  inodes: Map<string, FileNode>;
  holographicMapping: Map<string, string>;
  witness: string;
}

export interface FileNode {
  id: string;
  name: string;
  type: 'file' | 'directory' | 'symlink' | 'device';
  size: number;
  permissions: number;
  owner: string;
  group: string;
  createdAt: Date;
  modifiedAt: Date;
  content: Buffer | null;
  children: Map<string, FileNode>;
  holographicContext: Map<string, any>;
}

export interface NetworkStack {
  id: string;
  type: 'tcp' | 'udp' | 'holographic';
  interfaces: Map<string, NetworkInterface>;
  routes: Map<string, NetworkRoute>;
  connections: Map<string, NetworkConnection>;
  protocols: Map<string, NetworkProtocol>;
  holographicRouting: Map<string, string>;
  witness: string;
}

export interface NetworkInterface {
  id: string;
  name: string;
  type: 'ethernet' | 'wifi' | 'bluetooth' | 'holographic';
  macAddress: string;
  ipAddress: string;
  subnet: string;
  status: 'up' | 'down' | 'error';
  speed: number;
  holographicMapping: Map<string, any>;
}

export interface NetworkRoute {
  id: string;
  destination: string;
  gateway: string;
  interface: string;
  metric: number;
  holographicContext: Map<string, any>;
}

export interface NetworkConnection {
  id: string;
  localAddress: string;
  remoteAddress: string;
  protocol: string;
  state: 'established' | 'listening' | 'closed' | 'error';
  holographicContext: Map<string, any>;
}

export interface NetworkProtocol {
  id: string;
  name: string;
  version: string;
  capabilities: string[];
  holographicInterface: (data: any) => Promise<any>;
}

export interface SecurityContext {
  id: string;
  type: 'user' | 'group' | 'role' | 'policy';
  name: string;
  permissions: Map<string, string[]>;
  attributes: Map<string, any>;
  holographicIdentity: string;
  witness: string;
}

export interface ProcessManager {
  id: string;
  processes: Map<number, Process>;
  threads: Map<number, Thread>;
  scheduler: ProcessScheduler;
  memoryManager: MemoryManager;
  holographicContext: Map<string, any>;
}

export interface Process {
  pid: number;
  name: string;
  state: 'running' | 'blocked' | 'ready' | 'terminated';
  priority: number;
  memory: ProcessMemory;
  files: ProcessFiles;
  context: ProcessContext;
  holographicContext: Map<string, any>;
  witness: string;
}

export interface Thread {
  tid: number;
  pid: number;
  state: 'running' | 'blocked' | 'ready' | 'terminated';
  priority: number;
  stack: Buffer;
  registers: Map<string, any>;
  holographicContext: Map<string, any>;
}

export interface ProcessMemory {
  text: MemorySegment;
  data: MemorySegment;
  heap: MemorySegment;
  stack: MemorySegment;
  holographicMapping: Map<string, string>;
}

export interface MemorySegment {
  base: number;
  size: number;
  permissions: string;
  holographicContext: Map<string, any>;
}

export interface ProcessFiles {
  stdin: FileDescriptor;
  stdout: FileDescriptor;
  stderr: FileDescriptor;
  files: Map<number, FileDescriptor>;
  holographicMapping: Map<string, string>;
}

export interface FileDescriptor {
  fd: number;
  file: FileNode;
  position: number;
  flags: number;
  holographicContext: Map<string, any>;
}

export interface ProcessContext {
  pid: number;
  parentPid: number;
  coreId: string;
  securityContext: SecurityContext;
  holographicContext: Map<string, any>;
}

export interface ProcessScheduler {
  algorithm: 'round_robin' | 'priority' | 'holographic';
  quantum: number;
  readyQueue: Process[];
  blockedQueue: Process[];
  holographicOptimization: boolean;
}

export interface MemoryManager {
  algorithm: 'buddy' | 'slab' | 'holographic';
  totalMemory: number;
  freeMemory: number;
  allocatedMemory: number;
  holographicMapping: Map<string, string>;
}

export interface SystemContext {
  fileSystems: Map<string, FileSystem>;
  networkStacks: Map<string, NetworkStack>;
  securityContexts: Map<string, SecurityContext>;
  processManager: ProcessManager;
  holographicState: Map<string, any>;
  unifiedContext: Map<string, any>;
}

export class SystemPrimitives {
  private context: SystemContext;
  private atlasEncoder: Atlas12288Encoder;
  private witnessGenerator: WitnessGenerator;
  private hardwarePrimitives: CompleteHardwarePrimitives;
  private crossLayerCommunicators: Map<string, (data: any) => Promise<void>>;

  constructor(hardwarePrimitives: CompleteHardwarePrimitives) {
    this.atlasEncoder = new Atlas12288Encoder();
    this.witnessGenerator = new WitnessGenerator();
    this.hardwarePrimitives = hardwarePrimitives;
    this.crossLayerCommunicators = new Map();
    this.initializeContext();
    this.setupCrossLayerCommunication();
  }

  /**
   * Initialize system context
   */
  private async initializeContext(): Promise<void> {
    this.context = {
      fileSystems: new Map(),
      networkStacks: new Map(),
      securityContexts: new Map(),
      processManager: {
        id: 'process_manager_0',
        processes: new Map(),
        threads: new Map(),
        scheduler: {
          algorithm: 'holographic',
          quantum: 100,
          readyQueue: [],
          blockedQueue: [],
          holographicOptimization: true
        },
        memoryManager: {
          algorithm: 'holographic',
          totalMemory: 8 * 1024 * 1024 * 1024, // 8GB
          freeMemory: 8 * 1024 * 1024 * 1024,
          allocatedMemory: 0,
          holographicMapping: new Map()
        },
        holographicContext: new Map()
      },
      holographicState: new Map(),
      unifiedContext: new Map()
    };

    // Initialize file systems
    await this.initializeFileSystems();
    
    // Initialize network stacks
    await this.initializeNetworkStacks();
    
    // Initialize security contexts
    await this.initializeSecurityContexts();
    
    // Initialize process manager
    await this.initializeProcessManager();
    
    // Initialize holographic state
    await this.initializeHolographicState();
  }

  /**
   * Initialize file systems
   */
  private async initializeFileSystems(): Promise<void> {
    const fsConfigs = [
      { id: 'rootfs', type: 'holographic', mountpoint: '/', capacity: 100 * 1024 * 1024 * 1024 },
      { id: 'homefs', type: 'holographic', mountpoint: '/home', capacity: 50 * 1024 * 1024 * 1024 },
      { id: 'tmpfs', type: 'holographic', mountpoint: '/tmp', capacity: 10 * 1024 * 1024 * 1024 },
      { id: 'varfs', type: 'holographic', mountpoint: '/var', capacity: 20 * 1024 * 1024 * 1024 }
    ];

    for (const config of fsConfigs) {
      const fs: FileSystem = {
        id: config.id,
        type: config.type as any,
        mountpoint: config.mountpoint,
        capacity: config.capacity,
        used: 0,
        inodes: new Map(),
        holographicMapping: new Map(),
        witness: await this.generateSystemWitness(config.id, 'filesystem')
      };

      // Create root directory
      const rootNode: FileNode = {
        id: `${config.id}_root`,
        name: '/',
        type: 'directory',
        size: 0,
        permissions: 0o755,
        owner: 'root',
        group: 'root',
        createdAt: new Date(),
        modifiedAt: new Date(),
        content: null,
        children: new Map(),
        holographicContext: new Map()
      };

      fs.inodes.set('/', rootNode);
      this.context.fileSystems.set(config.id, fs);
    }
  }

  /**
   * Initialize network stacks
   */
  private async initializeNetworkStacks(): Promise<void> {
    const networkConfigs = [
      { id: 'tcp_stack', type: 'tcp' },
      { id: 'udp_stack', type: 'udp' },
      { id: 'holographic_stack', type: 'holographic' }
    ];

    for (const config of networkConfigs) {
      const stack: NetworkStack = {
        id: config.id,
        type: config.type as any,
        interfaces: new Map(),
        routes: new Map(),
        connections: new Map(),
        protocols: new Map(),
        holographicRouting: new Map(),
        witness: await this.generateSystemWitness(config.id, 'network')
      };

      // Add default interface
      const interface_: NetworkInterface = {
        id: `${config.id}_eth0`,
        name: 'eth0',
        type: 'ethernet',
        macAddress: '00:11:22:33:44:55',
        ipAddress: '192.168.1.100',
        subnet: '192.168.1.0/24',
        status: 'up',
        speed: 1000,
        holographicMapping: new Map()
      };

      stack.interfaces.set('eth0', interface_);

      // Add default route
      const route: NetworkRoute = {
        id: `${config.id}_default`,
        destination: '0.0.0.0/0',
        gateway: '192.168.1.1',
        interface: 'eth0',
        metric: 1,
        holographicContext: new Map()
      };

      stack.routes.set('default', route);

      this.context.networkStacks.set(config.id, stack);
    }
  }

  /**
   * Initialize security contexts
   */
  private async initializeSecurityContexts(): Promise<void> {
    const securityConfigs = [
      { id: 'root', type: 'user', name: 'root', permissions: ['*'] },
      { id: 'admin', type: 'user', name: 'admin', permissions: ['read', 'write', 'execute'] },
      { id: 'user', type: 'user', name: 'user', permissions: ['read', 'write'] },
      { id: 'guest', type: 'user', name: 'guest', permissions: ['read'] },
      { id: 'system', type: 'group', name: 'system', permissions: ['*'] },
      { id: 'users', type: 'group', name: 'users', permissions: ['read', 'write'] }
    ];

    for (const config of securityConfigs) {
      const securityContext: SecurityContext = {
        id: config.id,
        type: config.type as any,
        name: config.name,
        permissions: new Map(),
        attributes: new Map(),
        holographicIdentity: await this.generateHolographicIdentity(config.id),
        witness: await this.generateSystemWitness(config.id, 'security')
      };

      // Set permissions
      for (const permission of config.permissions) {
        securityContext.permissions.set(permission, ['*']);
      }

      this.context.securityContexts.set(config.id, securityContext);
    }
  }

  /**
   * Initialize process manager
   */
  private async initializeProcessManager(): Promise<void> {
    // Create init process
    const initProcess: Process = {
      pid: 1,
      name: 'init',
      state: 'running',
      priority: 0,
      memory: {
        text: { base: 0x400000, size: 1024 * 1024, permissions: 'r-x', holographicContext: new Map() },
        data: { base: 0x500000, size: 1024 * 1024, permissions: 'rw-', holographicContext: new Map() },
        heap: { base: 0x600000, size: 1024 * 1024, permissions: 'rw-', holographicContext: new Map() },
        stack: { base: 0x700000, size: 1024 * 1024, permissions: 'rw-', holographicContext: new Map() },
        holographicMapping: new Map()
      },
      files: {
        stdin: { fd: 0, file: this.getFileNode('/dev/stdin'), position: 0, flags: 0, holographicContext: new Map() },
        stdout: { fd: 1, file: this.getFileNode('/dev/stdout'), position: 0, flags: 0, holographicContext: new Map() },
        stderr: { fd: 2, file: this.getFileNode('/dev/stderr'), position: 0, flags: 0, holographicContext: new Map() },
        files: new Map(),
        holographicMapping: new Map()
      },
      context: {
        pid: 1,
        parentPid: 0,
        coreId: 'core0',
        securityContext: this.context.securityContexts.get('root')!,
        holographicContext: new Map()
      },
      holographicContext: new Map(),
      witness: await this.generateSystemWitness('1', 'process')
    };

    this.context.processManager.processes.set(1, initProcess);
    this.context.processManager.scheduler.readyQueue.push(initProcess);
  }

  /**
   * Initialize holographic state
   */
  private async initializeHolographicState(): Promise<void> {
    // Create holographic mappings for all system components
    for (const [fsId, fs] of this.context.fileSystems) {
      const atlasMetadata = await this.atlasEncoder.encodeContent({
        name: `filesystem_${fsId}`,
        data: JSON.stringify(fs),
        mimeType: 'application/hologram-filesystem'
      });

      this.context.holographicState.set(fsId, {
        atlas12288: atlasMetadata,
        conservationLaws: ['page_conservation', 'cycle_conservation'],
        witness: await this.witnessGenerator.generateSystemWitness(fs),
        crossLayerMapping: new Map()
      });
    }

    for (const [stackId, stack] of this.context.networkStacks) {
      const atlasMetadata = await this.atlasEncoder.encodeContent({
        name: `network_${stackId}`,
        data: JSON.stringify(stack),
        mimeType: 'application/hologram-network'
      });

      this.context.holographicState.set(stackId, {
        atlas12288: atlasMetadata,
        conservationLaws: ['page_conservation', 'cycle_conservation'],
        witness: await this.witnessGenerator.generateSystemWitness(stack),
        crossLayerMapping: new Map()
      });
    }
  }

  /**
   * Setup cross-layer communication
   */
  private setupCrossLayerCommunication(): void {
    this.crossLayerCommunicators.set('default', async (data: any) => {
      // Store in unified context
      this.context.unifiedContext.set(`${Date.now()}_${Math.random()}`, data);
      
      // Update holographic state
      const holographicData = await this.atlasEncoder.encodeContent({
        name: 'system_cross_layer_communication',
        data: JSON.stringify(data),
        mimeType: 'application/hologram-system-cross-layer'
      });
      
      this.context.holographicState.set(`system_cross_layer_${Date.now()}`, holographicData);
    });
  }

  /**
   * Generate system witness
   */
  private async generateSystemWitness(componentId: string, componentType: string): Promise<string> {
    const componentData = {
      id: componentId,
      type: componentType,
      timestamp: Date.now(),
      holographicContext: 'system_primitive'
    };

    return await this.witnessGenerator.generateSystemWitness(componentData);
  }

  /**
   * Generate holographic identity
   */
  private async generateHolographicIdentity(identityId: string): Promise<string> {
    const identityData = {
      id: identityId,
      timestamp: Date.now(),
      holographicContext: 'security_identity'
    };

    const atlasMetadata = await this.atlasEncoder.encodeContent({
      name: `identity_${identityId}`,
      data: JSON.stringify(identityData),
      mimeType: 'application/hologram-identity'
    });

    return atlasMetadata.conservationHash;
  }

  /**
   * Get file node
   */
  private getFileNode(path: string): FileNode {
    // Create a simple file node for device files
    return {
      id: `dev_${path.replace('/', '_')}`,
      name: path,
      type: 'device',
      size: 0,
      permissions: 0o666,
      owner: 'root',
      group: 'root',
      createdAt: new Date(),
      modifiedAt: new Date(),
      content: null,
      children: new Map(),
      holographicContext: new Map()
    };
  }

  /**
   * Get system context
   */
  getContext(): SystemContext {
    return this.context;
  }

  /**
   * Get holographic state
   */
  getHolographicState(): Map<string, any> {
    return this.context.holographicState;
  }

  /**
   * Get unified context
   */
  getUnifiedContext(): Map<string, any> {
    return this.context.unifiedContext;
  }

  /**
   * Execute system operation with holographic verification
   */
  async executeSystemOperation(operation: string, data: any): Promise<any> {
    // Verify holographic state
    const holographicState = this.context.holographicState.get(operation);
    if (!holographicState) {
      // Create new holographic state for operation
      const atlasMetadata = await this.atlasEncoder.encodeContent({
        name: `system_operation_${operation}`,
        data: JSON.stringify(data),
        mimeType: 'application/hologram-system-operation'
      });

      this.context.holographicState.set(operation, {
        atlas12288: atlasMetadata,
        conservationLaws: ['page_conservation', 'cycle_conservation'],
        witness: await this.witnessGenerator.generateSystemWitness({ operation, data }),
        crossLayerMapping: new Map()
      });
    }

    // Execute operation
    const result = await this.performSystemOperation(operation, data);
    
    // Update holographic state
    await this.updateHolographicState(operation, result);
    
    // Cross-layer communication
    await this.crossLayerCommunicators.get('default')?.({
      operation,
      result,
      timestamp: Date.now()
    });

    return result;
  }

  /**
   * Perform system operation
   */
  private async performSystemOperation(operation: string, data: any): Promise<any> {
    switch (operation) {
      case 'create_file':
        return await this.createFile(data.path, data.content);
      case 'read_file':
        return await this.readFile(data.path);
      case 'write_file':
        return await this.writeFile(data.path, data.content);
      case 'delete_file':
        return await this.deleteFile(data.path);
      case 'list_directory':
        return await this.listDirectory(data.path);
      case 'create_process':
        return await this.createProcess(data.name, data.program);
      case 'terminate_process':
        return await this.terminateProcess(data.pid);
      case 'send_network':
        return await this.sendNetwork(data.destination, data.data);
      case 'receive_network':
        return await this.receiveNetwork(data.interface);
      case 'authenticate':
        return await this.authenticate(data.credentials);
      case 'authorize':
        return await this.authorize(data.user, data.resource, data.action);
      default:
        throw new Error(`Unsupported system operation: ${operation}`);
    }
  }

  /**
   * Create file
   */
  private async createFile(path: string, content: Buffer): Promise<any> {
    const fs = this.context.fileSystems.get('rootfs');
    if (!fs) throw new Error('Root filesystem not found');

    const fileNode: FileNode = {
      id: `file_${Date.now()}`,
      name: path.split('/').pop() || 'unnamed',
      type: 'file',
      size: content.length,
      permissions: 0o644,
      owner: 'root',
      group: 'root',
      createdAt: new Date(),
      modifiedAt: new Date(),
      content,
      children: new Map(),
      holographicContext: new Map()
    };

    fs.inodes.set(path, fileNode);
    fs.used += content.length;

    return { success: true, path, size: content.length };
  }

  /**
   * Read file
   */
  private async readFile(path: string): Promise<any> {
    const fs = this.context.fileSystems.get('rootfs');
    if (!fs) throw new Error('Root filesystem not found');

    const fileNode = fs.inodes.get(path);
    if (!fileNode) throw new Error(`File not found: ${path}`);

    return { content: fileNode.content, size: fileNode.size };
  }

  /**
   * Write file
   */
  private async writeFile(path: string, content: Buffer): Promise<any> {
    const fs = this.context.fileSystems.get('rootfs');
    if (!fs) throw new Error('Root filesystem not found');

    const fileNode = fs.inodes.get(path);
    if (!fileNode) throw new Error(`File not found: ${path}`);

    const oldSize = fileNode.size;
    fileNode.content = content;
    fileNode.size = content.length;
    fileNode.modifiedAt = new Date();

    fs.used = fs.used - oldSize + content.length;

    return { success: true, path, size: content.length };
  }

  /**
   * Delete file
   */
  private async deleteFile(path: string): Promise<any> {
    const fs = this.context.fileSystems.get('rootfs');
    if (!fs) throw new Error('Root filesystem not found');

    const fileNode = fs.inodes.get(path);
    if (!fileNode) throw new Error(`File not found: ${path}`);

    fs.used -= fileNode.size;
    fs.inodes.delete(path);

    return { success: true, path };
  }

  /**
   * List directory
   */
  private async listDirectory(path: string): Promise<any> {
    const fs = this.context.fileSystems.get('rootfs');
    if (!fs) throw new Error('Root filesystem not found');

    const dirNode = fs.inodes.get(path);
    if (!dirNode || dirNode.type !== 'directory') {
      throw new Error(`Directory not found: ${path}`);
    }

    return Array.from(dirNode.children.keys());
  }

  /**
   * Create process
   */
  private async createProcess(name: string, program: number[]): Promise<any> {
    const nextPid = Math.max(...Array.from(this.context.processManager.processes.keys())) + 1;
    
    const process: Process = {
      pid: nextPid,
      name,
      state: 'ready',
      priority: 1,
      memory: {
        text: { base: 0x400000 + nextPid * 0x100000, size: 1024 * 1024, permissions: 'r-x', holographicContext: new Map() },
        data: { base: 0x500000 + nextPid * 0x100000, size: 1024 * 1024, permissions: 'rw-', holographicContext: new Map() },
        heap: { base: 0x600000 + nextPid * 0x100000, size: 1024 * 1024, permissions: 'rw-', holographicContext: new Map() },
        stack: { base: 0x700000 + nextPid * 0x100000, size: 1024 * 1024, permissions: 'rw-', holographicContext: new Map() },
        holographicMapping: new Map()
      },
      files: {
        stdin: { fd: 0, file: this.getFileNode('/dev/stdin'), position: 0, flags: 0, holographicContext: new Map() },
        stdout: { fd: 1, file: this.getFileNode('/dev/stdout'), position: 0, flags: 0, holographicContext: new Map() },
        stderr: { fd: 2, file: this.getFileNode('/dev/stderr'), position: 0, flags: 0, holographicContext: new Map() },
        files: new Map(),
        holographicMapping: new Map()
      },
      context: {
        pid: nextPid,
        parentPid: 1,
        coreId: 'core0',
        securityContext: this.context.securityContexts.get('user')!,
        holographicContext: new Map()
      },
      holographicContext: new Map(),
      witness: await this.generateSystemWitness(nextPid.toString(), 'process')
    };

    this.context.processManager.processes.set(nextPid, process);
    this.context.processManager.scheduler.readyQueue.push(process);

    return { success: true, pid: nextPid, name };
  }

  /**
   * Terminate process
   */
  private async terminateProcess(pid: number): Promise<any> {
    const process = this.context.processManager.processes.get(pid);
    if (!process) throw new Error(`Process not found: ${pid}`);

    process.state = 'terminated';
    this.context.processManager.processes.delete(pid);

    // Remove from scheduler queues
    const readyIndex = this.context.processManager.scheduler.readyQueue.findIndex(p => p.pid === pid);
    if (readyIndex !== -1) {
      this.context.processManager.scheduler.readyQueue.splice(readyIndex, 1);
    }

    const blockedIndex = this.context.processManager.scheduler.blockedQueue.findIndex(p => p.pid === pid);
    if (blockedIndex !== -1) {
      this.context.processManager.scheduler.blockedQueue.splice(blockedIndex, 1);
    }

    return { success: true, pid };
  }

  /**
   * Send network data
   */
  private async sendNetwork(destination: string, data: Buffer): Promise<any> {
    const stack = this.context.networkStacks.get('tcp_stack');
    if (!stack) throw new Error('TCP stack not found');

    const connection: NetworkConnection = {
      id: `conn_${Date.now()}`,
      localAddress: '192.168.1.100:8080',
      remoteAddress: destination,
      protocol: 'tcp',
      state: 'established',
      holographicContext: new Map()
    };

    stack.connections.set(connection.id, connection);

    return { success: true, connectionId: connection.id, bytes: data.length };
  }

  /**
   * Receive network data
   */
  private async receiveNetwork(interfaceName: string): Promise<any> {
    const stack = this.context.networkStacks.get('tcp_stack');
    if (!stack) throw new Error('TCP stack not found');

    const interface_ = stack.interfaces.get(interfaceName);
    if (!interface_) throw new Error(`Interface not found: ${interfaceName}`);

    return { data: Buffer.from('Network data received'), source: '192.168.1.1:8080' };
  }

  /**
   * Authenticate user
   */
  private async authenticate(credentials: any): Promise<any> {
    const { username, password } = credentials;
    
    // Simple authentication logic
    if (username === 'root' && password === 'root') {
      return { success: true, user: 'root', token: 'auth_token_' + Date.now() };
    } else if (username === 'user' && password === 'user') {
      return { success: true, user: 'user', token: 'auth_token_' + Date.now() };
    } else {
      return { success: false, error: 'Invalid credentials' };
    }
  }

  /**
   * Authorize user action
   */
  private async authorize(user: string, resource: string, action: string): Promise<any> {
    const securityContext = this.context.securityContexts.get(user);
    if (!securityContext) return { success: false, error: 'User not found' };

    const permissions = securityContext.permissions.get(action);
    if (!permissions) return { success: false, error: 'Permission denied' };

    return { success: true, user, resource, action };
  }

  /**
   * Update holographic state
   */
  private async updateHolographicState(operation: string, result: any): Promise<void> {
    const currentState = this.context.holographicState.get(operation);
    if (!currentState) return;

    // Update state with operation result
    currentState.lastOperation = operation;
    currentState.lastResult = result;
    currentState.lastUpdate = Date.now();

    // Regenerate witness
    currentState.witness = await this.witnessGenerator.generateSystemWitness({
      operation,
      result,
      timestamp: Date.now()
    });

    this.context.holographicState.set(operation, currentState);
  }
}
