include "kt.mm";
include "kct.mm";
include "ax-cb1.mm";
include "wctr.mm";
include "trud.mm";
include "id.mm";
include "syl2anc.mm";

theorem trul(tr: $term$ R, ts: $term$ S) {
  assume trul.1: $|- ( T. , R ) |= S$;





  do {
    ts;
    tr;
    kt;
    tr;
    tr;
    kt;
    tr;
    ts;
    kt;
    tr;
    kct;
    trul.1;
    ax-cb1;
    wctr;
    #;
    trud;
    tr;
    @0;
    id;
    trul.1;
    syl2anc;
  };

  return $|- R |= S$;
}
