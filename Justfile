format-bib:
    bibtool -F -r .bibtoolrsc -i ./references.bib -o references.bib
    sed -i '1{/^$/d}' references.bib

cache:
    lake exe cache get
    LAKE_CONFIG=lake-cache.toml lake cache get --service ffl --max-revs=100 \
      --repo FormalizedFormalLogic/Foundation --package Foundation \
      || echo "Foundation's cache is incomplete; the build will compile the rest from source"
    LAKE_CONFIG=lake-cache.toml lake cache get --service ffl --max-revs=100 \
      --repo FormalizedFormalLogic/ProvabilityLogic \
      || echo "ProvabilityLogic's cache is incomplete; the build will compile the rest from source"

import-graph:
    lake exe graph --to ProvabilityLogic import_graph.dot import_graph.png import_graph.pdf import_graph.html

cloc:
    cloc --include-lang=Lean ProvabilityLogic/

mk-all:
    lake exe mk_all --module

forgive:
    lake exe forgive ProvabilityLogic

docs:
    rm -rf .lake/build/doc .lake/build/doc-data
    lake build ProvabilityLogic:docs
