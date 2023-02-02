# agda-algebras (gh-pages branch)

This branch is used to generate the html documentation.

Workflow:

```
git checkout master
./generate.html
git checkout gh-pages
\cp html/* .
git checkout master _includes/UALib.Links.md  # Don't forget to update UALib.Links.md!
git add *.md *.html _includes/UALib.Links.md
git commit -m "update html documentation"
git push
```

