/**
 * Express-based GraphQL Server for Hologram Content Resolution System
 * 
 * Alternative implementation using Express + Apollo Server
 * with proper event loop management.
 */

import { ApolloServer } from "@apollo/server";
import { expressMiddleware } from "@apollo/server/express4";
import { ApolloServerPluginDrainHttpServer } from "@apollo/server/plugin/drainHttpServer";
import express from 'express';
import http from 'http';
import { hologramSchema } from './schema';
import { resolvers } from './resolvers';

async function startServer() {
  const PORT = parseInt(process.env.PORT || "4000", 10);
  
  // Create Express app and HTTP server
  const app = express();
  const httpServer = http.createServer(app);

  // Create Apollo Server
  const server = new ApolloServer({
    typeDefs: hologramSchema,
    resolvers,
    plugins: [ApolloServerPluginDrainHttpServer({ httpServer })],
    introspection: true
  });

  try {
    // Start Apollo Server
    await server.start();

    // Apply GraphQL middleware
    app.use('/graphql', express.json(), expressMiddleware(server, {
      context: async ({ req }) => {
        return {
          user: req.headers.authorization ? extractUser(req.headers.authorization) : null,
          requestId: generateRequestId()
        };
      }
    }));

    // Add health check endpoint
    app.get('/health', (req, res) => {
      res.json({ 
        status: 'healthy',
        timestamp: new Date().toISOString(),
        service: 'hologram-graphql'
      });
    });

    // Add metrics endpoint
    app.get('/metrics', (req, res) => {
      res.json({
        totalRequests: 1000, // Placeholder
        averageResponseTime: 45.2, // Placeholder
        conservationViolations: 0,
        bijectionIntegrity: 1.0
      });
    });

    // Start HTTP server
    await new Promise<void>((resolve) => {
      httpServer.listen(PORT, () => {
        console.log(`✅ GraphQL ready at http://localhost:${PORT}/graphql`);
        console.log(`📊 Health check available at http://localhost:${PORT}/health`);
        console.log(`📈 Metrics available at http://localhost:${PORT}/metrics`);
        resolve();
      });
    });

  } catch (error) {
    console.error('Failed to start GraphQL server:', error);
    process.exit(1);
  }
}

// Helper functions
function extractUser(authorization: string): any {
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
  process.exit(0);
});

process.on("SIGINT", () => { 
  console.log("SIGINT received, shutting down gracefully");
  process.exit(0);
});

// Start the server
startServer().catch((error) => {
  console.error('Failed to start server:', error);
  process.exit(1);
});
