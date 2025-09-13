# Use Node.js 22 Alpine image
FROM node:22-alpine

# Set working directory
WORKDIR /app

# Copy package files
COPY package.json package-lock.json* ./

# Install dependencies
RUN npm install

# Copy source code
COPY . .

# Create a script to run all commands
RUN echo '#!/bin/sh' > run-all.sh && \
    echo 'echo "=== Installing dependencies ==="' >> run-all.sh && \
    echo 'npm install' >> run-all.sh && \
    echo 'echo "=== Stamping blueprint fingerprint ==="' >> run-all.sh && \
    echo 'npm run stamp:blueprint' >> run-all.sh && \
    echo 'echo "=== Running tests ==="' >> run-all.sh && \
    echo 'npm test' >> run-all.sh && \
    echo 'echo "=== Validating blueprint ==="' >> run-all.sh && \
    echo 'npm run validate atlas-12288/blueprint/blueprint.json' >> run-all.sh && \
    chmod +x run-all.sh

# Default command
CMD ["./run-all.sh"]
