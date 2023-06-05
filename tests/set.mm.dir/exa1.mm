include "wi.mm";
include "ax-1.mm";
include "eximi.mm";

theorem exa1(wph: wff ph, wps: wff ps, vx: setvar x) {





  do {
    wph;
    wps;
    wph;
    wi;
    vx;
    wph;
    wps;
    ax-1;
    eximi;
  };

  return |- "( E. x ph -> E. x ( ps -> ph ) )";
}
