include "nf5ri.mm";
include "eximdh.mm";

theorem eximd(wph: wff ph, wps: wff ps, wch: wff ch, vx: setvar x) {
  assume eximd.1: |- "F/ x ph";
  assume eximd.2: |- "( ph -> ( ps -> ch ) )";





  do {
    wph;
    wps;
    wch;
    vx;
    wph;
    vx;
    eximd.1;
    nf5ri;
    eximd.2;
    eximdh;
  };

  return |- "( ph -> ( E. x ps -> E. x ch ) )";
}
