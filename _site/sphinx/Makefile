# Minimal makefile for Sphinx documentation
#

# You can set these variables from the command line.
SPHINXOPTS    =
SPHINXBUILD   = python3 -msphinx
SPHINXPROJ    = ualib.gitlab.io
SOURCEDIR     = .
BUILDDIR      = _build

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

VENVDIR := .venv
export PATH := $(VENVDIR)/bin:$(PATH)

install-deps:
	#test -f $(VENVDIR)/bin/pip || python3 -m venv $(VENVDIR)
	pip3 install sphinx
	pip3 install sphinxcontrib-bibtex sphinxcontrib-proof sphinxcontrib-tikz
	pip3 install https://bitbucket.org/gebner/pygments-main/get/default.tar.gz#egg=Pygments
	#pip3 install 'wheel>=0.29' # needed for old ubuntu versions, https://github.com/pallets/markupsafe/issues/59
.PHONY: help Makefile

images:
	cd latex_images && make copy_images

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)





# SPHINXOPTS    =
# SPHINXBUILD   = python -msphinx
# SPHINXPROJ    = ualib.gitlab.io
# SOURCEDIR     = .
# BUILDDIR      = _build

# help:
# 	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

# VENVDIR := .venv
# export PATH := $(VENVDIR)/bin:$(PATH)

# install-deps:
# 	test -f $(VENVDIR)/bin/pip || python3 -m venv $(VENVDIR)
# 	pip install https://bitbucket.org/gebner/pygments-main/get/default.tar.gz#egg=Pygments
# 	pip install sphinx
# 	pip install sphinxcontrib-bibtex sphinxcontrib-proof sphinxcontrib-tikz
# .PHONY: help Makefile

# images:
# 	cd latex_images && make copy_images

# %: Makefile
# 	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)
