include "kct.mm";
include "ax-cb2.mm";
include "wctl.mm";
include "wctr.mm";
include "simpl.mm";
include "syl.mm";

theorem simpld(tr: $term$ R, ts: $term$ S, tt: $term$ T) {
  assume simpld.1: $|- R |= ( S , T )$;





  do {
    tr;
    ts;
    tt;
    kct;
    #;
    ts;
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
    simpl;
    syl;
  };

  return $|- R |= S$;
}
