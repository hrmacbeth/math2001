# The Mechanics of Proof

This repository contains the Lean code for the book [The Mechanics of Proof](https://hrmacbeth.github.io/math2001), by [Heather Macbeth](https://faculty.fordham.edu/hmacbeth1), developed for the course Math 2001 at Fordham University.

The Lean files corresponding to each chapter of the book are in the folder [`Math2001`](https://github.com/hrmacbeth/math2001/tree/main/Math2001).

You can run the code on the web using GitHub Codespaces, by clicking this link:

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/hrmacbeth/math2001)

(You will be prompted to sign in to GitHub.) This is the easiest way to get started if you have never used Lean before.  The workspace takes several minutes to set up and auto-install the Lean mathematical library; wait for the build to finish.  Your codespaces are listed at [github.com/codespaces](https://github.com/codespaces).

You can also run the code locally in a [dev container](https://containers.dev) with Docker or podman.  Install the [Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) extension for VS Code, clone this repository, open it in VS Code, and run "Dev Containers: Reopen in Container".

- Docker: choose the default configuration, `.devcontainer/devcontainer.json`.
- Podman (rootless): set the VS Code setting `dev.containers.dockerPath` to `podman`, then choose the configuration `.devcontainer/podman/devcontainer.json`.
