

axiom ax-jca(tr: $term$ R, ts: $term$ S, tt: $term$ T) {
  assume ax-jca.1: $|- R |= S$;
  assume ax-jca.2: $|- R |= T$;

  return $|-$ $R |= ( S , T )$;
}
