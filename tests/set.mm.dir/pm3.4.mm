include "wa.mm";
include "simpr.mm";
include "a1d.mm";

theorem pm3.4(wph: wff ph, wps: wff ps) {





  do {
    wph;
    wps;
    wa;
    wps;
    wph;
    wph;
    wps;
    simpr;
    a1d;
  };

  return |- "( ( ph /\\ ps ) -> ( ph -> ps ) )";
}
