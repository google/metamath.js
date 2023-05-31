include "wsb.mm";
include "biimpi.mm";
include "sbimi.mm";
include "biimpri.mm";
include "impbii.mm";

theorem sbbii(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x, vy: $setvar$ y) {
  assume sbbii.1: $|- ( ph <-> ps )$;





  do {
    wph;
    vx;
    vy;
    wsb;
    wps;
    vx;
    vy;
    wsb;
    wph;
    wps;
    vx;
    vy;
    wph;
    wps;
    sbbii.1;
    biimpi;
    sbimi;
    wps;
    wph;
    vx;
    vy;
    wph;
    wps;
    sbbii.1;
    biimpri;
    sbimi;
    impbii;
  };

  return $|-$ $( [ y / x ] ph <-> [ y / x ] ps )$;
}
