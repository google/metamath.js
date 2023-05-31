
axiom wct(ts: $term$ S, tt: $term$ T) {
  assume wct.1: $|- S : bool$;
  assume wct.2: $|- T : bool$;

  return $|-$ $( S , T ) : bool$;
}
