include "dp53.mm";

theorem oadp35lemg(wvp: $term$ p, wva0: $term$ a0, wva1: $term$ a1, wva2: $term$ a2, wvb0: $term$ b0, wvb1: $term$ b1, wvb2: $term$ b2, wvc0: $term$ c0, wvc1: $term$ c1, wvc2: $term$ c2, wvp0: $term$ p0) {
  assume oadp35lem.1: $|- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )$;
  assume oadp35lem.2: $|- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )$;
  assume oadp35lem.3: $|- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )$;
  assume oadp35lem.4: $|- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) )$;
  assume oadp35lem.5: $|- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )$;





  do {
    wvp;
    wva0;
    wva1;
    wva2;
    wvb0;
    wvb1;
    wvb2;
    wvc0;
    wvc1;
    wvc2;
    oadp35lem.1;
    oadp35lem.2;
    oadp35lem.3;
    oadp35lem.5;
    dp53;
  };

  return $|-$ $p =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) )$;
}
