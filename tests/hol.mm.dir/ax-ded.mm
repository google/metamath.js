
axiom ax-ded(tr: $term$ R, ts: $term$ S, tt: $term$ T) {
  assume ax-ded.1: $|- ( R , S ) |= T$;
  assume ax-ded.2: $|- ( R , T ) |= S$;

  return $|-$ $R |= ( ( = S ) T )$;
}
