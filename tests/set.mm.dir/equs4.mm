include "weq.mm";
include "wi.mm";
include "wal.mm";
include "wex.mm";
include "wa.mm";
include "ax6e.mm";
include "exintr.mm";
include "mpi.mm";

theorem equs4(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {





  do {
    vx;
    vy;
    weq;
    #;
    wph;
    wi;
    vx;
    wal;
    @0;
    vx;
    wex;
    @0;
    wph;
    wa;
    vx;
    wex;
    vx;
    vy;
    ax6e;
    @0;
    wph;
    vx;
    exintr;
    mpi;
  };

  return '|-' "( A. x ( x = y -> ph ) -> E. x ( x = y /\\ ph ) )";
}
