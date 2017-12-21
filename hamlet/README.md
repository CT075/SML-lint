An extension of the HaMLet compiler to help find isomorphisms in code.

# The below features are not yet implemented

# Functionality and Usage
The notable functionality is the ability to compile SML code into graphs. In particular, SML code gets compiled into a graph representation formatted to be visualized by [GraphViz](http://www.graphviz.org/)'s "dot" tool.

To compile SML code into graphs and visualize them using GraphViz,
- load `sources.cm` into an interactive SML/NJ session (`sml -m sources.cm`)
- run `Sml.compileGraphFile "path-to-sml-file.sml";`. This will create a file `path-to-sml-file.sml.gv` containing the graph in [GraphViz's DOT format](http://www.graphviz.org/content/dot-language).
- to visualize this graph, make sure you have [GraphViz](http://www.graphviz.org/) installed, then run it through `dot`. For example, `dot -Tpng path-to-sml-file.sml.gv -o graph.png`


# Code files
There are a scary number of files, but most aren't of interest; they are left over from the HaMLet compiler's additional functionality. In the future it would be good to take these extra files out and leave only what we need. In the meantime, here is a rough guide of the files/directories of interest:
- `main/Sml.sml`: the structure which exports top-level functionality of the compiler. At some point we should update `main/Main.sml` to call the functionality in here (as it already does for all of HaMLet's other functionality) if we want to allow this to be a standalone command-line program.
- `graph/`: contains files which, given SML ASTs, produce graph representations.