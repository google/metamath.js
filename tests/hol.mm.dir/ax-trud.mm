

axiom ax-trud(tr: term R) {
  assume ax-trud.1: |- "R : bool";

  return '|-' "R |= T.";
}
