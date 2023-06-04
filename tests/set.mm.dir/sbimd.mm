include "weq.mm";
include "wi.mm";
include "wa.mm";
include "wex.mm";
include "wsb.mm";
include "imim2d.mm";
include "anim2d.mm";
include "eximd.mm";
include "anim12d.mm";
include "df-sb.mm";
include "3imtr4g.mm";

theorem sbimd(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, vx: 'setvar' x, vy: 'setvar' y) {
  assume sbimd.1: |- "F/ x ph";
  assume sbimd.2: |- "( ph -> ( ps -> ch ) )";





  do {
    wph;
    vx;
    vy;
    weq;
    #;
    wps;
    wi;
    #;
    @0;
    wps;
    wa;
    #;
    vx;
    wex;
    #;
    wa;
    @0;
    wch;
    wi;
    #;
    @0;
    wch;
    wa;
    #;
    vx;
    wex;
    #;
    wa;
    wps;
    vx;
    vy;
    wsb;
    wch;
    vx;
    vy;
    wsb;
    wph;
    @1;
    @4;
    @3;
    @6;
    wph;
    wps;
    wch;
    @0;
    sbimd.2;
    imim2d;
    wph;
    @2;
    @5;
    vx;
    sbimd.1;
    wph;
    wps;
    wch;
    @0;
    sbimd.2;
    anim2d;
    eximd;
    anim12d;
    wps;
    vx;
    vy;
    df-sb;
    wch;
    vx;
    vy;
    df-sb;
    3imtr4g;
  };

  return '|-' "( ph -> ( [ y / x ] ps -> [ y / x ] ch ) )";
}
