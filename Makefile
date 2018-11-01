ISABELLE ?= isabelle

ifdef SAIL_DIR
SNAPSHOTS_DIR ?= $(SAIL_DIR)/snapshots/isabelle
endif

ifdef SNAPSHOTS_DIR
LEM_LIB_DIR ?= $(SNAPSHOTS_DIR)/lib/lem
SAIL_LIB_DIR ?= $(SNAPSHOTS_DIR)/lib/sail
AARCH64_DIR ?= $(SNAPSHOTS_DIR)/aarch64
endif

path_msg := "Unable to locate theory dependencies.  Please either set the \
SNAPSHOTS_DIR environment variable to point to the snapshots/isabelle directory \
in a checkout of the Sail repository, or set the variables LEM_LIB_DIR, \
SAIL_LIB_DIR, and AARCH64_DIR individually."

check:
ifndef LEM_LIB_DIR
	$(error $(path_msg))
endif
ifndef SAIL_LIB_DIR
	$(error $(path_msg))
endif
ifndef AARCH64_DIR
	$(error $(path_msg))
endif
	$(ISABELLE) build -d $(LEM_LIB_DIR) -d $(SAIL_LIB_DIR) -d $(AARCH64_DIR) -D .
