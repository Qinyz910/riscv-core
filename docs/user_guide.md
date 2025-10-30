# User Guide

Use this guide to document how contributors and users interact with the project. Each section is intentionally left as a template to be expanded as tooling and workflows stabilize.

## Prerequisites
- List required toolchains (e.g., RISC-V GCC, simulators) and supported host platforms.
- Capture environment variables and package dependencies.

## Repository Setup
1. Clone the repository and select the appropriate branch.
2. Install dependencies using your preferred package manager or provided scripts.
3. Verify tool versions with helper commands or scripts.

## Building the RTL
- Describe any build orchestration (Make, CMake, Python scripts).
- Note output locations for synthesized netlists or intermediate artifacts.

## Simulation & Verification
- Summarize available simulation back-ends (Verilator, VCS, etc.).
- Show how to run smoke tests, directed tests, and regression suites.
- Document where logs, waveforms, and coverage data are produced.

## Testing & Continuous Integration
- Outline required tests before submitting changes.
- Link to CI dashboards or status badges when available.

## Documentation Workflow
- Explain how markdown documentation is structured and published.
- Add instructions for contributing diagrams or design collateral.

## Troubleshooting & FAQ
- Capture common setup or runtime issues and their resolutions.
- Maintain a list of active debugging tips and contact points.
