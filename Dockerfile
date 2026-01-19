# Use a clean, standard Ubuntu base
FROM ubuntu:22.04

# Prevent interactive prompts
ENV DEBIAN_FRONTEND=noninteractive

# 1. Install System Dependencies
RUN apt-get update && apt-get install -y     curl     git     python3     python3-pip     python3-numpy     python3-scipy     python3-tqdm     && rm -rf /var/lib/apt/lists/*

# 2. Install Elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:v4.14.0

# Add Lean to PATH
ENV PATH="/root/.elan/bin:$PATH"

# 3. Set up working directory
WORKDIR /app

# 4. Copy Manifests
COPY lean-toolchain lakefile.toml lake-manifest.json ./

# 5. Copy Source Code
# IMPORTANT: Copy the library root file explicitly!
COPY ContinuityEngine.lean ./
COPY ContinuityEngine ./ContinuityEngine
COPY Main.lean ./

# 6. Initialize & Build
# Update dependencies
RUN lake update

# Get binary cache (Critical for speed)
RUN lake exe cache get

# Build the project
RUN lake build ContinuityEngine

# 7. Verification Step
RUN echo "import ContinuityEngine.Bridge \n#check UnifiedBridge.structural_correspondence" | lake env lean --stdin

# Default command
CMD ["/bin/bash"]
