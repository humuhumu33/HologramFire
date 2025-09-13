/**
 * Unit tests for Placement functionality
 */

import { place } from '../src/adapters/hologram';
import { Placement } from '../src/types';

describe('Placement', () => {
  describe('place function', () => {
    it('should return at least 3 coordinates', () => {
      const id = 'test-id-123';
      const placements = place(id, { rows: 48, cols: 256 });
      
      expect(placements.length).toBeGreaterThanOrEqual(3);
    });

    it('should return coordinates within valid ranges', () => {
      const id = 'test-id-456';
      const placements = place(id, { rows: 48, cols: 256 });
      
      placements.forEach((p: Placement) => {
        expect(p.r).toBeGreaterThanOrEqual(0);
        expect(p.r).toBeLessThan(48);
        expect(p.c).toBeGreaterThanOrEqual(0);
        expect(p.c).toBeLessThan(256);
      });
    });

    it('should have at least 2 distinct rows', () => {
      const id = 'test-id-789';
      const placements = place(id, { rows: 48, cols: 256 });
      
      const rows = new Set(placements.map((p: any) => p.r));
      expect(rows.size).toBeGreaterThanOrEqual(2);
    });

    it('should be deterministic for the same ID', () => {
      const id = 'deterministic-test-id';
      const placements1 = place(id, { rows: 48, cols: 256 });
      const placements2 = place(id, { rows: 48, cols: 256 });
      
      expect(placements1).toEqual(placements2);
    });

    it('should be different for different IDs', () => {
      const id1 = 'test-id-1';
      const id2 = 'test-id-2';
      const placements1 = place(id1, { rows: 48, cols: 256 });
      const placements2 = place(id2, { rows: 48, cols: 256 });
      
      expect(placements1).not.toEqual(placements2);
    });

    it('should include parity placements when specified', () => {
      const id = 'test-id-with-parity';
      const placements = place(id, { rows: 48, cols: 256, parity: 2 });
      
      expect(placements.length).toBeGreaterThanOrEqual(5); // 3 data + 2 parity
    });

    it('should handle edge case IDs', () => {
      const edgeCases = [
        '',
        'a',
        'very-long-id-that-might-cause-issues-with-hashing-algorithms',
        'id-with-special-chars!@#$%^&*()',
        'id-with-unicode-🚀🌟⚡',
      ];
      
      edgeCases.forEach(id => {
        const placements = place(id, { rows: 48, cols: 256 });
        
        expect(placements.length).toBeGreaterThanOrEqual(3);
        placements.forEach((p: Placement) => {
          expect(p.r).toBeGreaterThanOrEqual(0);
          expect(p.r).toBeLessThan(48);
          expect(p.c).toBeGreaterThanOrEqual(0);
          expect(p.c).toBeLessThan(256);
        });
      });
    });

    it('should distribute placements across the grid', () => {
      const id = 'distribution-test-id';
      const placements = place(id, { rows: 48, cols: 256 });
      
      // Check that placements are not all clustered in one area
      const rowSpread = Math.max(...placements.map((p: any) => p.r)) - Math.min(...placements.map((p: any) => p.r));
      const colSpread = Math.max(...placements.map((p: any) => p.c)) - Math.min(...placements.map((p: any) => p.c));
      
      // At least some spread across rows and columns
      expect(rowSpread).toBeGreaterThan(0);
      expect(colSpread).toBeGreaterThan(0);
    });

    it('should handle different grid sizes', () => {
      const id = 'grid-size-test';
      const smallGrid = place(id, { rows: 4, cols: 8 });
      const largeGrid = place(id, { rows: 48, cols: 256 });
      
      expect(smallGrid.length).toBeGreaterThanOrEqual(3);
      expect(largeGrid.length).toBeGreaterThanOrEqual(3);
      
      smallGrid.forEach((p: Placement) => {
        expect(p.r).toBeGreaterThanOrEqual(0);
        expect(p.r).toBeLessThan(4);
        expect(p.c).toBeGreaterThanOrEqual(0);
        expect(p.c).toBeLessThan(8);
      });
      
      largeGrid.forEach((p: Placement) => {
        expect(p.r).toBeGreaterThanOrEqual(0);
        expect(p.r).toBeLessThan(48);
        expect(p.c).toBeGreaterThanOrEqual(0);
        expect(p.c).toBeLessThan(256);
      });
    });
  });
});
