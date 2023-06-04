include "wsb.mm";
include "weq.mm";
include "wi.mm";
include "wa.mm";
include "wex.mm";
include "df-sb.mm";
include "simprbi.mm";

theorem sb1(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {





  do {
    wph;
    vx;
    vy;
    wsb;
    vx;
    vy;
    weq;
    #;
    wph;
    wi;
    @0;
    wph;
    wa;
    vx;
    wex;
    wph;
    vx;
    vy;
    df-sb;
    simprbi;
  };

  return '|-' "( [ y / x ] ph -> E. x ( x = y /\\ ph ) )";
}
