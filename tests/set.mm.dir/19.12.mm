include "wal.mm";
include "wex.mm";
include "nfa1.mm";
include "nfex.mm";
include "sp.mm";
include "eximi.mm";
include "alrimi.mm";

theorem 19.12(wph: wff ph, vx: setvar x, vy: setvar y) {





  do {
    wph;
    vy;
    wal;
    #;
    vx;
    wex;
    wph;
    vx;
    wex;
    vy;
    @0;
    vy;
    vx;
    wph;
    vy;
    nfa1;
    nfex;
    @0;
    wph;
    vx;
    wph;
    vy;
    sp;
    eximi;
    alrimi;
  };

  return |- "( E. x A. y ph -> A. y E. x ph )";
}
