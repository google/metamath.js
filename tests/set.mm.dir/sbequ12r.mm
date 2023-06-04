include "wsb.mm";
include "wb.mm";
include "weq.mm";
include "sbequ12.mm";
include "bicomd.mm";
include "equcoms.mm";

theorem sbequ12r(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {





  do {
    wph;
    vy;
    vx;
    wsb;
    #;
    wph;
    wb;
    vy;
    vx;
    vy;
    vx;
    weq;
    wph;
    @0;
    wph;
    vy;
    vx;
    sbequ12;
    bicomd;
    equcoms;
  };

  return '|-' "( x = y -> ( [ x / y ] ph <-> ph ) )";
}
