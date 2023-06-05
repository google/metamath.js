include "wsb.mm";
include "weq.mm";
include "wi.mm";
include "wa.mm";
include "wex.mm";
include "df-sb.mm";
include "simplbi.mm";
include "com12.mm";

theorem sbequ2(wph: wff ph, vx: setvar x, vy: setvar y) {





  do {
    wph;
    vx;
    vy;
    wsb;
    #;
    vx;
    vy;
    weq;
    #;
    wph;
    @0;
    @1;
    wph;
    wi;
    @1;
    wph;
    wa;
    vx;
    wex;
    wph;
    vx;
    vy;
    df-sb;
    simplbi;
    com12;
  };

  return |- "( x = y -> ( [ y / x ] ph -> ph ) )";
}
