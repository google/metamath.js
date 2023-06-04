include "wal.mm";
include "weq.mm";
include "wi.mm";
include "ax-5.mm";
include "ax-12.mm";
include "syl5.mm";

theorem ax12v(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {

  disjoint x y;
  disjoint ph y;



  do {
    wph;
    wph;
    vy;
    wal;
    vx;
    vy;
    weq;
    #;
    @0;
    wph;
    wi;
    vx;
    wal;
    wph;
    vy;
    ax-5;
    wph;
    vx;
    vy;
    ax-12;
    syl5;
  };

  return '|-' "( x = y -> ( ph -> A. x ( x = y -> ph ) ) )";
}
