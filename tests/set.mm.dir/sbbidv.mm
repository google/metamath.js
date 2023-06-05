include "wsb.mm";
include "biimpd.mm";
include "sbimdv.mm";
include "biimprd.mm";
include "impbid.mm";

theorem sbbidv(wph: wff ph, wps: wff ps, wch: wff ch, vx: setvar x, vy: setvar y) {
  assume sbbidv.1: |- "( ph -> ( ps <-> ch ) )";

  disjoint ph x;



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
    wph;
    wps;
    wch;
    sbbidv.1;
    biimpd;
    sbimdv;
    wph;
    wch;
    wps;
    vx;
    vy;
    wph;
    wps;
    wch;
    sbbidv.1;
    biimprd;
    sbimdv;
    impbid;
  };

  return |- "( ph -> ( [ y / x ] ps <-> [ y / x ] ch ) )";
}
