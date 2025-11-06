# CAGE-SEV Documentation

Welcome to the CAGE-SEV documentation. This directory contains comprehensive guides for setting up, building, and understanding the CAGE-SEV confidential computing kernel.

## 📚 Table of Contents

### Getting Started
- **[Preparation Guide](Preparation.md)** - Complete setup guide for development environment
- **[Build Guide](Build.md)** - Building the kernel and components
- **[SEV Installation](install-sev.md)** - SEV-specific setup instructions

### Development
- **[Debug Guide](Debug.md)** - Debugging techniques and tools
- **[Logging Usage](logging-usage.md)** - Using the logging system

### Architecture & Design
- **[Memory Layout](mem-layout.png)** - Visual memory layout diagram
- **[Paging](Paging.md)** - Memory paging implementation
- **[Address Management](address.md)** - Address space management

## 🚀 Quick Start

For new developers, follow this recommended reading order:

1. **[Preparation Guide](Preparation.md)** - Set up your development environment
2. **[Build Guide](Build.md)** - Build and test the kernel
3. **[Debug Guide](Debug.md)** - Learn debugging workflows

## 📋 Documentation Categories

### 🛠️ Setup & Installation
| Document | Description | Audience |
|----------|-------------|----------|
| [Preparation](Preparation.md) | Complete environment setup | New developers |
| [SEV Installation](install-sev.md) | SEV-specific configuration | AMD SNP users |

### 🔨 Development
| Document | Description | Audience |
|----------|-------------|----------|
| [Build Guide](Build.md) | Building components | All developers |
| [Debug Guide](Debug.md) | Debugging techniques | All developers |
| [Logging](logging-usage.md) | Logging system usage | All developers |

### 🏗️ Architecture
| Document | Description | Audience |
|----------|-------------|----------|
| [Paging](Paging.md) | Memory paging design | Kernel developers |
| [Address Management](address.md) | Address space handling | Kernel developers |
| [Memory Layout](mem-layout.png) | System memory organization | All developers |

## 🎯 Target Architectures

CAGE-SEV supports two confidential computing architectures:

- **Intel TDX** (Trust Domain Extensions)
- **AMD SNP** (Secure Nested Paging)

Architecture-specific instructions are clearly marked throughout the documentation.

## 🤝 Contributing to Documentation

When adding new documentation:

1. Place files in the appropriate category subdirectory
2. Update this README.md index
3. Follow the existing documentation style
4. Include code examples where applicable
5. Test all instructions on a clean environment

## 📞 Getting Help

- **Issues**: Open an issue on the GitHub repository
- **Discussions**: Use GitHub Discussions for questions
- **Documentation bugs**: File issues with the "documentation" label

## 📄 License

This documentation is part of the CAGE-SEV project and follows the same license terms.

---

*Last updated: November 2025*
