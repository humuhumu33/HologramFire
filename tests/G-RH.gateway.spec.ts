import { describe, it, expect } from "vitest";
import { enforceGateway, rhGatewayEnabled } from "../src/rh/Gateway";

describe("G-RH: Field-7 Gateway", () => {
  it("allows active classes when enabled", () => {
    process.env.RH_FIELD7_GATEWAY = "on";
    expect(enforceGateway(0, rhGatewayEnabled()).ok).toBe(true);
  });
  it("always allows when disabled", () => {
    process.env.RH_FIELD7_GATEWAY = "off";
    expect(enforceGateway(95, rhGatewayEnabled()).ok).toBe(true);
  });
});
