include "kct.mm";
include "adantr.mm";
include "ax-cb1.mm";
include "simpr.mm";
include "jca.mm";

theorem ct1(tr: $term$ R, ts: $term$ S, tt: $term$ T) {
  assume ct1.1: $|- R |= S$;
  assume ct1.2: $|- T : bool$;





  do {
    tr;
    tt;
    kct;
    ts;
    tt;
    tr;
    tt;
    ts;
    ct1.1;
    ct1.2;
    adantr;
    tr;
    tt;
    ts;
    tr;
    ct1.1;
    ax-cb1;
    ct1.2;
    simpr;
    jca;
  };

  return $|- ( R , T ) |= ( S , T )$;
}
