/**
 * Pretty-printing utilities for benchmark results
 * 
 * Provides colored, formatted output for throughput benchmark results
 * with pass/fail indicators and detailed metrics.
 */

import { RunStats, RunArgs } from './loadgen';

export interface ReportOptions {
  showLaneUtil?: boolean;
  showDetailed?: boolean;
  colorOutput?: boolean;
}

/**
 * ANSI color codes for terminal output
 */
const colors = {
  reset: '\x1b[0m',
  bright: '\x1b[1m',
  red: '\x1b[31m',
  green: '\x1b[32m',
  yellow: '\x1b[33m',
  blue: '\x1b[34m',
  magenta: '\x1b[35m',
  cyan: '\x1b[36m',
  white: '\x1b[37m',
  gray: '\x1b[90m',
};

/**
 * Colorize text if color output is enabled
 */
function colorize(text: string, color: string, enabled: boolean = true): string {
  return enabled ? `${color}${text}${colors.reset}` : text;
}

/**
 * Format large numbers with K/M suffixes
 */
function formatNumber(num: number): string {
  if (num >= 1000000) {
    return `${(num / 1000000).toFixed(1)}M`;
  } else if (num >= 1000) {
    return `${(num / 1000).toFixed(1)}k`;
  } else {
    return num.toString();
  }
}

/**
 * Format bytes with appropriate units
 */
function formatBytes(bytes: number): string {
  const units = ['B', 'KB', 'MB', 'GB'];
  let size = bytes;
  let unitIndex = 0;
  
  while (size >= 1024 && unitIndex < units.length - 1) {
    size /= 1024;
    unitIndex++;
  }
  
  return `${size.toFixed(1)}${units[unitIndex]}`;
}

/**
 * Create ASCII bar for lane utilization
 */
function createLaneBar(laneUtil: Array<{ lane: number; frames: number }>, maxWidth: number = 50): string {
  if (laneUtil.length === 0) return '';
  
  const maxFrames = Math.max(...laneUtil.map(l => l.frames));
  if (maxFrames === 0) return '█'.repeat(maxWidth);
  
  const bars = laneUtil.slice(0, 10).map(lane => {
    const ratio = lane.frames / maxFrames;
    const barLength = Math.round(ratio * maxWidth);
    return `L${lane.lane}:${'█'.repeat(barLength)}${'░'.repeat(maxWidth - barLength)}`;
  });
  
  return bars.join('\n');
}

/**
 * Print benchmark report header
 */
export function printHeader(args: RunArgs, options: ReportOptions = {}): void {
  const { colorOutput = true } = options;
  
  console.log();
  console.log(colorize('═'.repeat(60), colors.cyan, colorOutput));
  console.log(colorize('CTP-96 Bench — 25G Throughput Validation', colors.bright + colors.cyan, colorOutput));
  console.log(colorize('═'.repeat(60), colors.cyan, colorOutput));
  console.log();
  
  console.log(`Duration: ${colorize(`${args.durationSec}s`, colors.white, colorOutput)}`);
  console.log(`Lanes: ${colorize(args.lanes.toString(), colors.white, colorOutput)}`);
  console.log(`Payload: ${colorize(formatBytes(args.payloadBytes), colors.white, colorOutput)}`);
  console.log(`Batch: ${colorize(args.batch.toString(), colors.white, colorOutput)}`);
  console.log(`Window: ${colorize(`${args.windowMs}ms`, colors.white, colorOutput)}`);
  console.log(`Workers: ${colorize(args.workers.toString(), colors.white, colorOutput)}`);
  if (args.aggregateTo) {
    console.log(`Aggregate: ${colorize(formatBytes(args.aggregateTo), colors.white, colorOutput)}`);
  }
  console.log(`Target: ${colorize(`${args.targetGbps} Gb/s`, colors.white, colorOutput)}`);
  console.log();
}

/**
 * Print main benchmark results
 */
export function printResults(stats: RunStats, args: RunArgs, options: ReportOptions = {}): void {
  const { colorOutput = true, showLaneUtil = true, showDetailed = false } = options;
  
  // Main metrics line
  const gbpsColor = stats.gbps >= args.targetGbps ? colors.green : colors.red;
  const fpsColor = stats.fps >= 100000 ? colors.green : colors.yellow;
  const p99Color = stats.p99latencyMs <= 2.0 ? colors.green : colors.red;
  const cpuColor = stats.cpuPercent <= 80 ? colors.green : colors.yellow;
  
  console.log(colorize('📊 Results:', colors.bright + colors.white, colorOutput));
  console.log(
    `Gb/s: ${colorize(stats.gbps.toFixed(1), gbpsColor, colorOutput)} ` +
    `fps: ${colorize(formatNumber(stats.fps), fpsColor, colorOutput)} ` +
    `p50: ${colorize(`${stats.p50latencyMs.toFixed(2)}ms`, colors.white, colorOutput)} ` +
    `p99: ${colorize(`${stats.p99latencyMs.toFixed(2)}ms`, p99Color, colorOutput)} ` +
    `CPU: ${colorize(`${stats.cpuPercent.toFixed(1)}%`, cpuColor, colorOutput)}`
  );
  console.log();
  
  // Frame statistics
  const lossRate = stats.sent > 0 ? (stats.rejected / stats.sent) * 100 : 0;
  const lossColor = lossRate <= 2.0 ? colors.green : colors.red;
  
  console.log(colorize('📈 Frame Stats:', colors.bright + colors.white, colorOutput));
  console.log(
    `Sent: ${colorize(formatNumber(stats.sent), colors.white, colorOutput)} ` +
    `Delivered: ${colorize(formatNumber(stats.delivered), colors.green, colorOutput)} ` +
    `Rejected: ${colorize(formatNumber(stats.rejected), lossColor, colorOutput)}`
  );
  console.log(`Loss Rate: ${colorize(`${lossRate.toFixed(2)}%`, lossColor, colorOutput)}`);
  console.log();
  
  // Window settlement
  const windowEfficiency = stats.settleTotal > 0 ? (stats.settleClosed / stats.settleTotal) * 100 : 0;
  const windowColor = windowEfficiency >= 99 ? colors.green : colors.red;
  
  console.log(colorize('🪟 Window Settlement:', colors.bright + colors.white, colorOutput));
  console.log(
    `Windows: ${colorize(`${stats.settleClosed}`, colors.green, colorOutput)} ` +
    `closed / ${colorize(`${stats.settleTotal}`, colors.white, colorOutput)} ` +
    `total (${colorize(`${windowEfficiency.toFixed(1)}%`, windowColor, colorOutput)})`
  );
  console.log();
  
  // Lane utilization
  if (showLaneUtil && stats.laneUtil.length > 0) {
    console.log(colorize('🛤️  Lane Utilization (top 10):', colors.bright + colors.white, colorOutput));
    const topLanes = stats.laneUtil
      .sort((a, b) => b.frames - a.frames)
      .slice(0, 10);
    
    topLanes.forEach(lane => {
      const frames = formatNumber(lane.frames);
      console.log(`  L${lane.lane.toString().padStart(2)}: ${colorize(frames, colors.cyan, colorOutput)} frames`);
    });
    console.log();
  }
  
  // Detailed metrics
  if (showDetailed) {
    console.log(colorize('🔍 Detailed Metrics:', colors.bright + colors.white, colorOutput));
    console.log(`  Effective Throughput: ${stats.gbps.toFixed(3)} Gb/s`);
    console.log(`  Frame Rate: ${stats.fps.toFixed(0)} fps`);
    console.log(`  Payload Size: ${formatBytes(args.payloadBytes)}`);
    console.log(`  Batch Size: ${args.batch}`);
    console.log(`  Total Lanes: ${args.lanes}`);
    console.log(`  Worker Count: ${args.workers}`);
    console.log(`  Window Size: ${args.windowMs}ms`);
    console.log();
  }
}

/**
 * Print pass/fail summary with exit criteria
 */
export function printSummary(stats: RunStats, args: RunArgs, options: ReportOptions = {}): boolean {
  const { colorOutput = true } = options;
  
  console.log(colorize('🎯 Pass/Fail Criteria:', colors.bright + colors.white, colorOutput));
  
  const criteria = [
    {
      name: 'Throughput ≥ Target',
      value: `${stats.gbps.toFixed(1)} ≥ ${args.targetGbps}`,
      passed: stats.gbps >= args.targetGbps,
    },
    {
      name: 'P99 Latency ≤ 2ms',
      value: `${stats.p99latencyMs.toFixed(2)} ≤ 2.0`,
      passed: stats.p99latencyMs <= 2.0,
    },
    {
      name: 'Window Efficiency ≥ 99%',
      value: `${((stats.settleClosed / stats.settleTotal) * 100).toFixed(1)}% ≥ 99%`,
      passed: (stats.settleClosed / stats.settleTotal) >= 0.99,
    },
    {
      name: 'Loss Rate ≤ 2%',
      value: `${((stats.rejected / stats.sent) * 100).toFixed(2)}% ≤ 2%`,
      passed: (stats.rejected / stats.sent) <= 0.02,
    },
  ];
  
  let allPassed = true;
  
  criteria.forEach(criterion => {
    const status = criterion.passed ? '✅ PASS' : '❌ FAIL';
    const statusColor = criterion.passed ? colors.green : colors.red;
    const statusText = colorize(status, statusColor, colorOutput);
    
    console.log(`  ${statusText} ${criterion.name}: ${criterion.value}`);
    
    if (!criterion.passed) {
      allPassed = false;
    }
  });
  
  console.log();
  
  // Overall result
  if (allPassed) {
    console.log(colorize('🎉 BENCHMARK PASSED - All criteria met!', colors.bright + colors.green, colorOutput));
  } else {
    console.log(colorize('💥 BENCHMARK FAILED - Some criteria not met', colors.bright + colors.red, colorOutput));
  }
  
  console.log();
  
  return allPassed;
}

/**
 * Print complete benchmark report
 */
export function printReport(stats: RunStats, args: RunArgs, options: ReportOptions = {}): boolean {
  printHeader(args, options);
  printResults(stats, args, options);
  return printSummary(stats, args, options);
}

/**
 * Export results to JSON format
 */
export function exportToJson(stats: RunStats, args: RunArgs, timestamp: string = new Date().toISOString()): object {
  return {
    timestamp,
    args,
    stats,
    criteria: {
      throughputPassed: stats.gbps >= args.targetGbps,
      latencyPassed: stats.p99latencyMs <= 2.0,
      windowEfficiencyPassed: (stats.settleClosed / stats.settleTotal) >= 0.99,
      lossRatePassed: (stats.rejected / stats.sent) <= 0.02,
      overallPassed: stats.gbps >= args.targetGbps && 
                    stats.p99latencyMs <= 2.0 && 
                    (stats.settleClosed / stats.settleTotal) >= 0.99 && 
                    (stats.rejected / stats.sent) <= 0.02,
    },
  };
}

