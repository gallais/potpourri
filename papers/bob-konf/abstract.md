Concurrent programs destructively updating shared memory are
notoriously hard to get right. Concurrent separation logics
are logics with built-in notions of e.g. ownership of memory
regions, concurrent accesses, and lock mechanisms. They give
experts a way to verify a posteriori that complex concurrent
imperative programs hopefully abide by their formal
specification.

We will see how next generation languages let us get rid of
a posteriori verification in favour of a correct-by-construction
approach whereby the program is interactively built in a
specification-respecting dialogue with the compiler.
For this presentation we will be using [Idris 2](https://www.idris-lang.org/),
a general purpose functional language with an expressive
type system combining dependent types to enforce complex
invariants and linear logic to track resource usage.

We will demonstrate how a simple library can capture ideas
from concurrent separation logic by providing proof-carrying
concurrent primitives. These make it impossible to write into
memory one does not own or to release a lock without having
proven that its associated invariant has been re-established.
They also guarantee that whatever is read from the shared
memory is invariant-respecting.

This will culminate in worked out example e.g. the definition
of map-reduce primitives repeatedly and safely breaking down
a buffer into chunks that can be processed concurrently
and/or a naïve bank with concurrent cash machines.
