include "wsb.mm";
include "weq.mm";
include "wa.mm";
include "wex.mm";
include "sb1.mm";
include "exsimpr.mm";
include "syl.mm";

theorem spsbe(wph: wff ph, vx: setvar x, vy: setvar y) {





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
    wa;
    vx;
    wex;
    wph;
    vx;
    wex;
    wph;
    vx;
    vy;
    sb1;
    @0;
    wph;
    vx;
    exsimpr;
    syl;
  };

  return |- "( [ y / x ] ph -> E. x ph )";
}
