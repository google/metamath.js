include "wa.mm";
include "ancom.mm";
include "exbii.mm";

theorem exancom(wph: wff ph, wps: wff ps, vx: setvar x) {





  do {
    wph;
    wps;
    wa;
    wps;
    wph;
    wa;
    vx;
    wph;
    wps;
    ancom;
    exbii;
  };

  return |- "( E. x ( ph /\\ ps ) <-> E. x ( ps /\\ ph ) )";
}
