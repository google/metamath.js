include "kct.mm";
include "ax-cb1.mm";
include "simpl.mm";
include "adantl.mm";
include "jca.mm";

theorem ct2(tr: $term$ R, ts: $term$ S, tt: $term$ T) {
  assume ct1.1: $|- R |= S$;
  assume ct1.2: $|- T : bool$;





  do {
    tt;
    tr;
    kct;
    tt;
    ts;
    tt;
    tr;
    ct1.2;
    ts;
    tr;
    ct1.1;
    ax-cb1;
    simpl;
    tr;
    tt;
    ts;
    ct1.1;
    ct1.2;
    adantl;
    jca;
  };

  return $|- ( T , R ) |= ( T , S )$;
}
