
axiom ax-simpr(tr: $term$ R, ts: $term$ S) {
  assume ax-simpl.1: $|- R : bool$;
  assume ax-simpl.2: $|- S : bool$;

  return $|-$ $( R , S ) |= S$;
}
