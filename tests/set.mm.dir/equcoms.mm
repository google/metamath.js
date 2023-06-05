include "weq.mm";
include "equcomi.mm";
include "syl.mm";

theorem equcoms(wph: wff ph, vx: setvar x, vy: setvar y) {
  assume equcoms.1: |- "( x = y -> ph )";





  do {
    vy;
    vx;
    weq;
    vx;
    vy;
    weq;
    wph;
    vy;
    vx;
    equcomi;
    equcoms.1;
    syl;
  };

  return |- "( y = x -> ph )";
}
