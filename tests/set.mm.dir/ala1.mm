include "wi.mm";
include "ax-1.mm";
include "alimi.mm";

theorem ala1(wph: wff ph, wps: wff ps, vx: setvar x) {





  do {
    wph;
    wps;
    wph;
    wi;
    vx;
    wph;
    wps;
    ax-1;
    alimi;
  };

  return |- "( A. x ph -> A. x ( ps -> ph ) )";
}
