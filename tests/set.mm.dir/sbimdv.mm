include "weq.mm";
include "wi.mm";
include "wa.mm";
include "wex.mm";
include "wsb.mm";
include "imim2d.mm";
include "anim2d.mm";
include "eximdv.mm";
include "anim12d.mm";
include "df-sb.mm";
include "3imtr4g.mm";

theorem sbimdv(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, vx: $setvar$ x, vy: $setvar$ y) {
  assume sbimdv.2: $|- ( ph -> ( ps -> ch ) )$;

  disjoint ph x;



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
    sbimdv.2;
    imim2d;
    wph;
    @2;
    @5;
    vx;
    wph;
    wps;
    wch;
    @0;
    sbimdv.2;
    anim2d;
    eximdv;
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

  return $|-$ $( ph -> ( [ y / x ] ps -> [ y / x ] ch ) )$;
}
