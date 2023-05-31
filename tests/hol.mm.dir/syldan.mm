include "kct.mm";
include "ax-cb1.mm";
include "wctl.mm";
include "wctr.mm";
include "simpl.mm";
include "syl2anc.mm";

theorem syldan(ta: $term$ A, tr: $term$ R, ts: $term$ S, tt: $term$ T) {
  assume syldan.1: $|- ( R , S ) |= T$;
  assume syldan.2: $|- ( R , T ) |= A$;





  do {
    ta;
    tr;
    ts;
    kct;
    #;
    tr;
    tt;
    tr;
    ts;
    tr;
    ts;
    tt;
    @0;
    syldan.1;
    ax-cb1;
    #;
    wctl;
    tr;
    ts;
    @1;
    wctr;
    simpl;
    syldan.1;
    syldan.2;
    syl2anc;
  };

  return $|-$ $( R , S ) |= A$;
}
