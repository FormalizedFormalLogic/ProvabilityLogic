# Format and regenerate keys of references.bib
format-bib:
    bibtool -F -r .bibtoolrsc -i ./references.bib -o references.bib
    sed -i '1{/^$/d}' references.bib

# Download Mathlib's, Foundation's and this library's prebuilt artifacts (a miss is not an error)
cache:
    lake exe cache get
    LAKE_CONFIG=lake-cache.toml lake cache get --service ffl --max-revs=100 \
      --repo FormalizedFormalLogic/Foundation --package Foundation \
      || echo "Foundation's cache is incomplete; the build will compile the rest from source"
    LAKE_CONFIG=lake-cache.toml lake cache get --service ffl --max-revs=100 \
      --repo FormalizedFormalLogic/ProvabilityLogic \
      || echo "this library's cache is incomplete; the build will compile the rest from source"

# Move every dependency pin onto the upstream toolchain and re-resolve it; prints what moved
bump:
    python3 scripts/bump-deps.py

# Everything CI checks, on the build in this tree
check:
    lake build ProvabilityLogic
    lake env leanchecker ProvabilityLogic
    lake exe forgive ProvabilityLogic
    lake exe mk_all --module
    git diff --exit-code -- ProvabilityLogic.lean

# Generate the import graph of ProvabilityLogic as import_graph.{dot,png,pdf,html} (requires graphviz)
import-graph:
    lake exe graph --to ProvabilityLogic import_graph.dot import_graph.png import_graph.pdf import_graph.html

# Count lines of Lean source in ProvabilityLogic/, excluding blank and comment lines (requires cloc)
cloc:
    cloc --include-lang=Lean ProvabilityLogic/

# Regenerate ProvabilityLogic.lean to include all modules (run after adding/removing files)
mk-all:
    lake exe mk_all --module

# Audit the axioms every ProvabilityLogic declaration uses against forgive.yml
forgive:
    lake exe forgive ProvabilityLogic

# doc-gen4's marker files under `doc-data` outlive the HTML, so both directories go; otherwise a
# restored build cache leaves the documentation frozen.
#
# Generate the API documentation into .lake/build/doc (requires `lake build ProvabilityLogic` first)
docs:
    rm -rf .lake/build/doc .lake/build/doc-data
    lake build ProvabilityLogic:docs
