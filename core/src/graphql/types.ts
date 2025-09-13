/**
 * TypeScript types for GraphQL Content Resolution System
 */

export interface Content {
  id: string;
  name: string;
  encoding: string;
  data: string;
  witness: Witness;
  metadata: ContentMetadata;
}

export interface ContentMetadata {
  createdAt: string;
  updatedAt: string;
  size: number;
  mimeType?: string;
  checksum: string;
  atlas12288: Atlas12288Metadata;
}

export interface Atlas12288Metadata {
  page: number;
  cycle: number;
  r96Class: number;
  kleinWindow: number;
  conservationHash: string;
}

export interface Witness {
  id: string;
  proof: string;
  verificationTime: string;
  isValid: boolean;
  conservationProof: ConservationProof;
}

export interface ConservationProof {
  pageConservation: boolean;
  cycleConservation: boolean;
  kleinProbes: KleinProbe[];
  r96Classification: R96Proof;
}

export interface KleinProbe {
  windowId: number;
  result: boolean;
  value: number;
}

export interface R96Proof {
  inputClass: number;
  outputClass: number;
  compressionRatio: number;
  isValid: boolean;
}

export interface ResolutionStats {
  totalContent: number;
  totalResolutions: number;
  averageResolutionTime: number;
  conservationViolations: number;
  bijectionIntegrity: number;
}

export interface ContentResolutionEvent {
  content: Content;
  resolutionTime: number;
  method: string;
}

export interface ConservationViolationEvent {
  contentId: string;
  violationType: string;
  details: string;
  timestamp: string;
}

export interface SearchCriteria {
  mimeType?: string;
  r96Class?: number;
  page?: number;
  cycle?: number;
  limit: number;
  offset: number;
}
