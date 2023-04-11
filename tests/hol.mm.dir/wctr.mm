
axiom wctr(ts: $term$ S, tt: $term$ T) {
  assume wctl.1: $|- ( S , T ) : bool$;

  return $|-$ $T : bool$;
}
