// src/bench/report.ts
import type { RunStats, Metrics, LoadGenResult } from "../types.js";

export function printReport(title: string, s: RunStats) {
  console.log(`\n${title}`);
  console.log(`Gb/s=${s.gbps.toFixed(1)}  fps=${Math.round(s.fps)}  CPU=${s.cpuPercent.toFixed(0)}%`);
  console.log(`p50/p99 transport=${s.transport.p50}/${s.transport.p99} ms  storage=${s.storage.p50}/${s.storage.p99} ms  compute=${s.compute.p50}/${s.compute.p99} ms  e2e=${s.e2e.p50}/${s.e2e.p99} ms`);
  console.log(`sent=${s.sent} delivered=${s.delivered} rejected=${s.rejected}  windows: ${s.settleClosed}/${s.settleTotal}`);
  const top = s.laneUtil.slice(0,16).map(x=>`${x.lane}:${x.frames}`).join(", ");
  console.log(`lanes: ${top}`);
}

export interface PerformanceReporter {
  generateReport(metrics: Metrics, loadGenResult: LoadGenResult): void;
}

export function createReporter(options: { format: 'both' | 'console' | 'json' }): PerformanceReporter {
  return {
    generateReport(metrics: Metrics, loadGenResult: LoadGenResult) {
      console.log('\n📊 Performance Report');
      console.log('='.repeat(60));
      
      // Throughput
      console.log(`🚀 Throughput: ${metrics.throughputGbps.toFixed(1)} Gbit/s`);
      
      // Latency metrics
      console.log(`⏱️  Latency (p50/p99 ms):`);
      console.log(`   Transport: ${metrics.transport.p50Ms.toFixed(2)}/${metrics.transport.p99Ms.toFixed(2)}`);
      console.log(`   Storage:   ${metrics.storage.p50Ms.toFixed(2)}/${metrics.storage.p99Ms.toFixed(2)}`);
      console.log(`   Compute:   ${metrics.compute.p50Ms.toFixed(2)}/${metrics.compute.p99Ms.toFixed(2)}`);
      console.log(`   E2E:       ${metrics.e2e.p50Ms.toFixed(2)}/${metrics.e2e.p99Ms.toFixed(2)}`);
      
      // Transport stats
      console.log(`📡 Transport Stats:`);
      console.log(`   Frames: ${metrics.transport.framesSent} sent, ${metrics.transport.framesReceived} received`);
      console.log(`   Windows: ${metrics.transport.windowsClosed}/${metrics.transport.windowsTotal} closed`);
      console.log(`   Rejects: ${metrics.transport.rejects} (${((metrics.transport.rejects / metrics.transport.framesSent) * 100).toFixed(1)}%)`);
      
      // Storage stats
      console.log(`💾 Storage Stats:`);
      console.log(`   Operations: ${metrics.storage.puts} puts, ${metrics.storage.gets} gets, ${metrics.storage.repairs} repairs`);
      
      // Compute stats
      console.log(`⚡ Compute Stats:`);
      console.log(`   Kernels: ${metrics.compute.kernels}, Receipts: ${metrics.compute.receipts}`);
      
      console.log('='.repeat(60));
    }
  };
}