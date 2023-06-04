include "weq.mm";
include "wsb.mm";
include "wa.mm";
include "wi.mm";
include "wex.mm";
include "pm3.4.mm";
include "19.8a.mm";
include "df-sb.mm";
include "sylanbrc.mm";
include "ex.mm";

theorem sbequ1(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {





  do {
    vx;
    vy;
    weq;
    #;
    wph;
    wph;
    vx;
    vy;
    wsb;
    #;
    @0;
    wph;
    wa;
    #;
    @0;
    wph;
    wi;
    @2;
    vx;
    wex;
    @1;
    @0;
    wph;
    pm3.4;
    @2;
    vx;
    19.8a;
    wph;
    vx;
    vy;
    df-sb;
    sylanbrc;
    ex;
  };

  return '|-' "( x = y -> ( ph -> [ y / x ] ph ) )";
}
