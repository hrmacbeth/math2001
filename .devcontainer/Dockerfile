FROM mcr.microsoft.com/devcontainers/base:trixie

USER vscode

COPY lean-toolchain /tmp/lean/toolchain

# Default toolchain: latest stable Lean 4. The project toolchain is pre-installed
# so opening the workspace does not trigger a download.
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain stable \
 && ~/.elan/bin/elan toolchain install stable "$(cat /tmp/lean/toolchain)"

ENV PATH="/home/vscode/.elan/bin:${PATH}"
