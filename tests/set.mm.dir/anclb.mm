include "wa.mm";
include "ibar.mm";
include "pm5.74i.mm";

theorem anclb(wph: wff ph, wps: wff ps) {





  do {
    wph;
    wps;
    wph;
    wps;
    wa;
    wph;
    wps;
    ibar;
    pm5.74i;
  };

  return |- "( ( ph -> ps ) <-> ( ph -> ( ph /\\ ps ) ) )";
}
