/**
 * Standalone GraphQL Server for Hologram Content Resolution System
 * 
 * Implements the solid start pattern using Apollo Server standalone
 * to ensure the event loop stays alive and the server runs properly.
 */

import { ApolloServer } from "@apollo/server";
import { startStandaloneServer } from "@apollo/server/standalone";
import { hologramSchema } from './schema';
import { resolvers } from './resolvers-simple';

// Create Apollo Server instance
const server = new ApolloServer({ 
  typeDefs: hologramSchema, 
  resolvers,
  introspection: true,
  plugins: [
    // Add any plugins here if needed
  ]
});

// Start the server
async function startServer() {
  const PORT = parseInt(process.env.PORT || "4000", 10);
  
  try {
    const { url } = await startStandaloneServer(server, { 
      listen: { port: PORT },
      context: async ({ req }) => {
        // Add authentication, rate limiting, etc. here
        return {
          user: req.headers.authorization ? extractUser(req.headers.authorization) : null,
          requestId: generateRequestId()
        };
      }
    });

    console.log(`✅ GraphQL ready at ${url}`);
    console.log(`📊 Health check available at http://localhost:${PORT}/health`);
    console.log(`📈 Metrics available at http://localhost:${PORT}/metrics`);

  } catch (error) {
    console.error('Failed to start GraphQL server:', error);
    process.exit(1);
  }
}

// Helper functions
function extractUser(authorization: string): any {
  // Placeholder implementation
  // In a real implementation, this would decode JWT tokens, etc.
  return {
    id: 'user_123',
    name: 'Test User',
    permissions: ['read', 'write']
  };
}

function generateRequestId(): string {
  return `req_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
}

// Handle graceful shutdown
process.on("SIGTERM", () => { 
  console.log("SIGTERM received, shutting down gracefully");
  server.stop().then(() => process.exit(0));
});

process.on("SIGINT", () => { 
  console.log("SIGINT received, shutting down gracefully");
  server.stop().then(() => process.exit(0));
});

// Start the server
startServer().catch((error) => {
  console.error('Failed to start server:', error);
  process.exit(1);
});
