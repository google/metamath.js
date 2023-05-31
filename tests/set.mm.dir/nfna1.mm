include "wal.mm";
include "nfa1.mm";
include "nfn.mm";

theorem nfna1(wph: $wff$ ph, vx: $setvar$ x) {





  do {
    wph;
    vx;
    wal;
    vx;
    wph;
    vx;
    nfa1;
    nfn;
  };

  return $|-$ $F/ x -. A. x ph$;
}
