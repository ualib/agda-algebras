# agda 2.6.1, jekyll, ghc and google-chrome need to be installed in the system
main_dir = ${HOME}/git/lab/ualib/ualib.gitlab.io
main_html_dir = ${HOME}/git/lab/ualib/ualib.gitlab.io/html
app = ualib
tt_dir = ${HOME}/git/lab/ualib/TypeTopology/source
public_html_dir = ${HOME}/public_html


install : _site/$(app).html pdf/all/$(app).pdf agda/$(app).agda additionally
	cp $(main_dir)/_site/index.html $(public_html_dir)/$(app)-doc/
	cp $(main_dir)/_site/$(app).html $(public_html_dir)/$(app)-doc/
	cp $(main_dir)/_site/Universes.html $(public_html_dir)/$(app)-doc/
	cp $(main_dir)/_site/Agda.Primitive.html $(public_html_dir)/$(app)-doc/
	cp -r $(main_dir)/_site/css $(public_html_dir)/$(app)-doc/
	cp $(main_dir)/_site/LICENSE $(public_html_dir)/$(app)-doc/
	cp $(main_dir)/pdf/all/$(app).pdf $(public_html_dir)/$(app)-doc/
	chmod -R a+r $(public_html_dir)/$(app)-doc/
	./additionally

all : _site/$(app).html pdf/all/$(app).pdf agda/$(app).agda

additionally :
	touch additionally
	chmod +x additionally

_site/$(app).html : $(app).lagda
	$(info )
	$(info This will take a couple of minutes...)
	$(info )
	time agda --html --html-highlight=code $(app).lagda
	cp $(main_html_dir)/$(app).tex $(main_dir)/index.md
	mv $(main_html_dir)/$(app).tex $(main_dir)/$(app).md
	mv $(main_html_dir)/Universes.tex $(main_dir)/Universes.html
	mv $(main_html_dir)/Agda.Primitive.Cubical.html $(main_dir)/Agda.Primitive.Cubical.html
	mv $(main_html_dir)/Agda.Primitive.html $(main_dir)/Agda.Primitive.html
	mv $(main_html_dir)/Empty-Type.tex $(main_dir)/Empty-Type.html
	mv $(main_html_dir)/Identity-Type.tex $(main_dir)/Identity-Type.html
	mv $(main_html_dir)/MGS-Basic-UF.tex $(main_dir)/MGS-Basic-UF.html
	mv $(main_html_dir)/MGS-Embeddings.tex $(main_dir)/MGS-Embeddings.html
	mv $(main_html_dir)/MGS-Equivalence-Induction.tex $(main_dir)/MGS-Equivalence-Induction.html
	mv $(main_html_dir)/MGS-Equivalences.tex $(main_dir)/MGS-Equivalences.html
	mv $(main_html_dir)/MGS-FunExt-from-Univalence.tex $(main_dir)/MGS-FunExt-from-Univalence.html
	mv $(main_html_dir)/MGS-HAE.tex $(main_dir)/MGS-HAE.html
	mv $(main_html_dir)/MGS-hlevels.tex $(main_dir)/MGS-hlevels.html
	mv $(main_html_dir)/MGS-MLTT.tex $(main_dir)/MGS-MLTT.html
	mv $(main_html_dir)/MGS-More-FunExt-Consequences.tex $(main_dir)/MGS-More-FunExt-Consequences.html
	mv $(main_html_dir)/MGS-Powerset.tex $(main_dir)/MGS-Powerset.html
	mv $(main_html_dir)/MGS-Retracts.tex $(main_dir)/MGS-Retracts.html
	mv $(main_html_dir)/Sigma-Type.tex $(main_dir)/Sigma-Type.html
	mv $(main_html_dir)/Plus-Type.tex $(main_dir)/Plus-Type.html
	mv $(main_html_dir)/Natural-Numbers-Type.tex $(main_dir)/Natural-Numbers-Type.html
	mv $(main_html_dir)/MGS-Univalence.tex $(main_dir)/MGS-Univalence.html
	mv $(main_html_dir)/MGS-Subsingleton-Truncation.tex $(main_dir)/MGS-Subsingleton-Truncation.html
	mv $(main_html_dir)/MGS-Subsingleton-Theorems.tex $(main_dir)/MGS-Subsingleton-Theorems.html
	mv $(main_html_dir)/MGS-Solved-Exercises.tex $(main_dir)/MGS-Solved-Exercises.html
	mv $(main_html_dir)/Unit-Type.tex $(main_dir)/Unit-Type.html
	$(info If the following fails you may need to run `bundler update`)
	bundle exec jekyll build

pdf/all/$(app).pdf : _site/$(app).html
	$(info )
	$(info This will likely give errors which can be ignored...)
	$(info )
	mkdir -p $(main_dir)/pdf
	mkdir -p $(main_dir)/all
	google-chrome --headless --print-to-pdf="$(main_dir)/pdf/all/$(app).pdf" $(main_dir)/_site/$(app).html

agda/$(app).agda :  $(app).lagda
	mkdir -p $(main_dir)/agda
	ghc --make illiterator.hs
	cat $(main_dir)/$(app).lagda | $(main_dir)/illiterator > $(main_dir)/agda/$(app).agda

clean :
	rm -f *.o *.hi $(app).html index.html Universes.html Agda.Primitive.html
	rm -f Empty-Type.html Identity-Type.html MGS-Basic-UF.html MGS-Embeddings.html MGS-Equivalence-Induction.html
	rm -f MGS-Equivalences.html MGS-FunExt-from-Univalence.html MGS-HAE.html MGS-hlevels.html MGS-MLTT.html
	rm -f MGS-More-FunExt-Consequences.html MGS-Powerset.html MGS-Retracts.html MGS-Solved-Exercises.html
	rm -f MGS-Subsingleton-Theorems.html MGS-Subsingleton-Truncation.html MGS-Univalence.html
	rm -f Natural-Numbers-Type.html Plus-Type.html Sigma-Type.html Unit-Type.html
	rm -f $(main_dir)/Agda.Primitive.Cubical.html $(main_dir)/Agda.Primitive.html
	rm -f $(main_dir)/index.md $(main_dir)/$(app).md
	rm -f $(main_dir)/Universes.md
	touch $(main_dir)/$(app).lagda

cleanmore :
	rm -f *.agdai *.o *.hi $(app).html index.html Universes.html Agda.Primitive.html illiterator
	rm -f Empty-Type.html Identity-Type.html MGS-Basic-UF.html MGS-Embeddings.html MGS-Equivalence-Induction.html
	rm -f MGS-Equivalences.html MGS-FunExt-from-Univalence.html MGS-HAE.html MGS-hlevels.html MGS-MLTT.html
	rm -f MGS-More-FunExt-Consequences.html MGS-Powerset.html MGS-Retracts.html MGS-Solved-Exercises.html
	rm -f MGS-Subsingleton-Theorems.html MGS-Subsingleton-Truncation.html MGS-Univalence.html
	rm -f Natural-Numbers-Type.html Plus-Type.html Sigma-Type.html Unit-Type.html
	rm -f $(main_dir)/Agda.Primitive.Cubical.html $(main_dir)/Agda.Primitive.html
	rm -f $(main_dir)/index.md $(main_dir)/$(app).md
	rm -f $(main_dir)/Universes.md
	touch $(main_dir)/$(app).lagda

cleanmd :
	rm -f *.agdai *.o *.hi $(app).md index.md Universes.md Agda.Primitive.html illiterator
	rm -f Empty-Type.md Identity-Type.md MGS-Basic-UF.md MGS-Embeddings.md MGS-Equivalence-Induction.md
	rm -f MGS-Equivalences.md MGS-FunExt-from-Univalence.md MGS-HAE.md MGS-hlevels.md MGS-MLTT.md
	rm -f MGS-More-FunExt-Consequences.md MGS-Powerset.md MGS-Retracts.md MGS-Solved-Exercises.md
	rm -f MGS-Subsingleton-Theorems.md MGS-Subsingleton-Truncation.md MGS-Univalence.md
	rm -f Natural-Numbers-Type.md Plus-Type.md Sigma-Type.md Unit-Type.md
	rm -f $(main_dir)/Agda.Primitive.Cubical.html $(main_dir)/Agda.Primitive.html
	rm -f $(main_dir)/index.md $(main_dir)/$(app).md
	rm -f $(main_dir)/Universes.md
	touch $(main_dir)/$(app).lagda

