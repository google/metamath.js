include "wex.mm";
include "eximi.mm";
include "ax-mp.mm";

theorem eximii(wph: wff ph, wps: wff ps, vx: setvar x) {
  assume eximii.1: |- "E. x ph";
  assume eximii.2: |- "( ph -> ps )";





  do {
    wph;
    vx;
    wex;
    wps;
    vx;
    wex;
    eximii.1;
    wph;
    wps;
    vx;
    eximii.2;
    eximi;
    ax-mp;
  };

  return |- "E. x ps";
}
