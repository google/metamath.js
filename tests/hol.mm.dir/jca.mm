include "ax-jca.mm";

theorem jca(tr: $term$ R, ts: $term$ S, tt: $term$ T) {
  assume ax-jca.1: $|- R |= S$;
  assume ax-jca.2: $|- R |= T$;





  do {
    tr;
    ts;
    tt;
    ax-jca.1;
    ax-jca.2;
    ax-jca;
  };

  return $|-$ $R |= ( S , T )$;
}
