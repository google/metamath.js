include "wal.mm";
include "alimi.mm";
include "ax-11.mm";
include "syl.mm";

theorem hbal(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {
  assume hbal.1: |- "( ph -> A. x ph )";





  do {
    wph;
    vy;
    wal;
    #;
    wph;
    vx;
    wal;
    #;
    vy;
    wal;
    @0;
    vx;
    wal;
    wph;
    @1;
    vy;
    hbal.1;
    alimi;
    wph;
    vy;
    vx;
    ax-11;
    syl;
  };

  return '|-' "( A. y ph -> A. x A. y ph )";
}
