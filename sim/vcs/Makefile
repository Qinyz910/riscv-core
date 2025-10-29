.PHONY: run compile lint clean help

PYTHON ?= python3
SIM_ROOT := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
PROJECT_ROOT := $(abspath $(SIM_ROOT)/../..)
RUNNER := $(SIM_ROOT)/scripts/run_vcs.py

TEST ?= smoke
WAVE ?= 0
COVERAGE ?= 0
LINT ?= 0
PROGRAM ?=

RUN_FLAGS := --project-root $(PROJECT_ROOT) --sim-root $(SIM_ROOT) --test $(TEST)

ifeq ($(WAVE),1)
RUN_FLAGS += --wave
endif
ifeq ($(COVERAGE),1)
RUN_FLAGS += --coverage
endif
ifeq ($(LINT),1)
RUN_FLAGS += --lint
endif
ifneq ($(strip $(PROGRAM)),)
RUN_FLAGS += --program $(abspath $(PROGRAM))
endif

run:
	$(PYTHON) $(RUNNER) $(RUN_FLAGS) --action run

compile:
	$(PYTHON) $(RUNNER) $(RUN_FLAGS) --action compile

lint:
	$(PYTHON) $(RUNNER) $(RUN_FLAGS) --action compile --lint

clean:
	rm -rf $(SIM_ROOT)/out

help:
	@echo "Synopsys VCS flow make targets:"
	@echo "  make run TEST=<name> [WAVE=1] [COVERAGE=1] [LINT=1] [PROGRAM=/path/to/img]"
	@echo "  make compile TEST=<name>"
	@echo "  make lint TEST=<name>      # Compile with lint-only settings"
	@echo "  make clean                 # Remove generated artifacts"
