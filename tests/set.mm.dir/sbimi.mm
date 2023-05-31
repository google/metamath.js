include "weq.mm";
include "wi.mm";
include "wa.mm";
include "wex.mm";
include "wsb.mm";
include "imim2i.mm";
include "anim2i.mm";
include "eximi.mm";
include "anim12i.mm";
include "df-sb.mm";
include "3imtr4i.mm";

theorem sbimi(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x, vy: $setvar$ y) {
  assume sbimi.1: $|- ( ph -> ps )$;





  do {
    vx;
    vy;
    weq;
    #;
    wph;
    wi;
    #;
    @0;
    wph;
    wa;
    #;
    vx;
    wex;
    #;
    wa;
    @0;
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
    wph;
    vx;
    vy;
    wsb;
    wps;
    vx;
    vy;
    wsb;
    @1;
    @4;
    @3;
    @6;
    wph;
    wps;
    @0;
    sbimi.1;
    imim2i;
    @2;
    @5;
    vx;
    wph;
    wps;
    @0;
    sbimi.1;
    anim2i;
    eximi;
    anim12i;
    wph;
    vx;
    vy;
    df-sb;
    wps;
    vx;
    vy;
    df-sb;
    3imtr4i;
  };

  return $|-$ $( [ y / x ] ph -> [ y / x ] ps )$;
}
