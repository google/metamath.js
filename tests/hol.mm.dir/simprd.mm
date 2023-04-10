include "kct.mm";
include "ax-cb2.mm";
include "wctl.mm";
include "wctr.mm";
include "simpr.mm";
include "syl.mm";

theorem simprd(tr: $term$ R, ts: $term$ S, tt: $term$ T) {
  assume simpld.1: $|- R |= ( S , T )$;





  do {
    tr;
    ts;
    tt;
    kct;
    #;
    tt;
    simpld.1;
    ts;
    tt;
    ts;
    tt;
    @0;
    tr;
    simpld.1;
    ax-cb2;
    #;
    wctl;
    ts;
    tt;
    @1;
    wctr;
    simpr;
    syl;
  };

  return $|- R |= T$;
}
