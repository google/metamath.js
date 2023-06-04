

axiom wctl(ts: 'term' S, tt: 'term' T) {
  assume wctl.1: |- "( S , T ) : bool";

  return '|-' "S : bool";
}
