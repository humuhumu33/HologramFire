/**
 * Integration tests for Transport functionality
 */

import { createCTP, createVerifier } from '../src/adapters/hologram';
import { createPostcard, createPostcardWitness } from '../src/usecases/postcard';
import { mkBudget } from '../src/testkit';

describe('Transport Integration', () => {
  let ctp: any;
  let verifier: any;
  let postcard: any;
  let witness: any;

  beforeEach(async () => {
    ctp = await createCTP({
      nodeId: 'test-transport-node',
      lanes: 8,
      windowMs: 100,
    });
    
    verifier = await createVerifier();
    postcard = createPostcard('Transport test message', 'TestUser', 'TestRecipient');
    witness = await createPostcardWitness(postcard);
  });

  afterEach(async () => {
    if (ctp) {
      await ctp.close();
    }
  });

  describe('CTP handshake', () => {
    it('should perform successful handshake', async () => {
      const handshakeResult = await ctp.handshake({
        nodeId: 'test-transport-node',
        capabilities: ['transport', 'verification'],
      });
      
      expect(handshakeResult).toBe(true);
    });

    it('should handle handshake with different node info', async () => {
      const handshakeResult = await ctp.handshake({
        nodeId: 'different-node',
        capabilities: ['transport'],
      });
      
      expect(handshakeResult).toBe(true);
    });
  });

  describe('CTP send and receive', () => {
    it('should send and receive messages successfully', async () => {
      const budget = mkBudget(200, 25, 16);
      const lane = 2;
      
      // Send message
      const sendResult = await ctp.send({
        lane,
        payload: postcard.bytes,
        budget,
        attach: {
          r96: witness.r96,
          probes: witness.probes,
        },
      });
      
      expect(sendResult.lane).toBe(lane);
      expect(sendResult.attach).toBeDefined();
      
      // Receive message
      const recvResult = await ctp.recv();
      
      expect(recvResult.lane).toBe(lane);
      expect(recvResult.payload).toEqual(postcard.bytes);
      expect(recvResult.frame).toBeDefined();
      expect(recvResult.windowId).toBeDefined();
    });

    it('should verify Klein probe on received frame', async () => {
      const budget = mkBudget(200, 25, 16);
      const lane = 2;
      
      await ctp.send({
        lane,
        payload: postcard.bytes,
        budget,
        attach: {
          r96: witness.r96,
          probes: witness.probes,
        },
      });
      
      const recvResult = await ctp.recv();
      const kleinValid = verifier.klein(recvResult.frame);
      
      expect(kleinValid).toBe(true);
    });

    it('should verify r96 checksum on received payload', async () => {
      const budget = mkBudget(200, 25, 16);
      const lane = 2;
      
      await ctp.send({
        lane,
        payload: postcard.bytes,
        budget,
        attach: {
          r96: witness.r96,
          probes: witness.probes,
        },
      });
      
      const recvResult = await ctp.recv();
      const expectedR96 = verifier.r96(recvResult.payload);
      
      expect(expectedR96).toBe(witness.r96);
    });
  });

  describe('CTP settlement', () => {
    it('should settle window and return closed receipt', async () => {
      const budget = mkBudget(200, 25, 16);
      const lane = 2;
      
      await ctp.send({
        lane,
        payload: postcard.bytes,
        budget,
        attach: {
          r96: witness.r96,
          probes: witness.probes,
        },
      });
      
      const recvResult = await ctp.recv();
      const receipt = await ctp.settle(recvResult.windowId);
      
      expect(receipt.ok).toBe(true);
      expect(receipt.windowClosed).toBe(true);
      expect(receipt.budgetAfter).toBeDefined();
      expect(receipt.details).toBeDefined();
      expect(receipt.details.operation).toBe('ctp_settle');
      expect(receipt.details.windowId).toBe(recvResult.windowId);
    });

    it('should handle multiple settlements', async () => {
      const budget = mkBudget(200, 25, 16);
      const lane = 2;
      
      // Send and settle first message
      await ctp.send({
        lane,
        payload: postcard.bytes,
        budget,
        attach: {
          r96: witness.r96,
          probes: witness.probes,
        },
      });
      
      const recvResult1 = await ctp.recv();
      const receipt1 = await ctp.settle(recvResult1.windowId);
      
      // Send and settle second message
      const postcard2 = createPostcard('Second message', 'User2', 'Recipient2');
      const witness2 = await createPostcardWitness(postcard2);
      
      await ctp.send({
        lane,
        payload: postcard2.bytes,
        budget,
        attach: {
          r96: witness2.r96,
          probes: witness2.probes,
        },
      });
      
      const recvResult2 = await ctp.recv();
      const receipt2 = await ctp.settle(recvResult2.windowId);
      
      expect(receipt1.ok).toBe(true);
      expect(receipt2.ok).toBe(true);
      expect(receipt1.details.windowId).not.toBe(receipt2.details.windowId);
    });
  });

  describe('Budget enforcement', () => {
    it('should reject send with insufficient budget', async () => {
      const zeroBudget = mkBudget(0, 0, 0);
      const lane = 2;
      
      await expect(
        ctp.send({
          lane,
          payload: postcard.bytes,
          budget: zeroBudget,
          attach: {
            r96: witness.r96,
            probes: witness.probes,
          },
        })
      ).rejects.toThrow('Insufficient budget');
    });

    it('should accept send with adequate budget', async () => {
      const adequateBudget = mkBudget(200, 25, 16);
      const lane = 2;
      
      const sendResult = await ctp.send({
        lane,
        payload: postcard.bytes,
        budget: adequateBudget,
        attach: {
          r96: witness.r96,
          probes: witness.probes,
        },
      });
      
      expect(sendResult.lane).toBe(lane);
    });
  });

  describe('Multiple lanes', () => {
    it('should handle messages on different lanes', async () => {
      const budget = mkBudget(200, 25, 16);
      const lane1 = 1;
      const lane2 = 3;
      
      // Send on lane 1
      await ctp.send({
        lane: lane1,
        payload: postcard.bytes,
        budget,
        attach: {
          r96: witness.r96,
          probes: witness.probes,
        },
      });
      
      // Send on lane 2
      const postcard2 = createPostcard('Lane 2 message', 'User2', 'Recipient2');
      const witness2 = await createPostcardWitness(postcard2);
      
      await ctp.send({
        lane: lane2,
        payload: postcard2.bytes,
        budget,
        attach: {
          r96: witness2.r96,
          probes: witness2.probes,
        },
      });
      
      // Receive both messages
      const recvResult1 = await ctp.recv();
      const recvResult2 = await ctp.recv();
      
      expect([recvResult1.lane, recvResult2.lane]).toContain(lane1);
      expect([recvResult1.lane, recvResult2.lane]).toContain(lane2);
    });
  });

  describe('Error handling', () => {
    it('should handle receive when no messages are available', async () => {
      await expect(ctp.recv()).rejects.toThrow('No messages in queue');
    });

    it('should handle close operation', async () => {
      await expect(ctp.close()).resolves.not.toThrow();
    });
  });
});
