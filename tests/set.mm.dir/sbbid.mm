include "wsb.mm";
include "biimpd.mm";
include "sbimd.mm";
include "biimprd.mm";
include "impbid.mm";

theorem sbbid(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, vx: $setvar$ x, vy: $setvar$ y) {
  assume sbbid.1: $|- F/ x ph$;
  assume sbbid.2: $|- ( ph -> ( ps <-> ch ) )$;





  do {
    wph;
    wps;
    vx;
    vy;
    wsb;
    wch;
    vx;
    vy;
    wsb;
    wph;
    wps;
    wch;
    vx;
    vy;
    sbbid.1;
    wph;
    wps;
    wch;
    sbbid.2;
    biimpd;
    sbimd;
    wph;
    wch;
    wps;
    vx;
    vy;
    sbbid.1;
    wph;
    wps;
    wch;
    sbbid.2;
    biimprd;
    sbimd;
    impbid;
  };

  return $|-$ $( ph -> ( [ y / x ] ps <-> [ y / x ] ch ) )$;
}
