include "wi.mm";
include "wa.mm";
include "ex.mm";

theorem exp31(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume exp31.1: |- "( ( ( ph /\\ ps ) /\\ ch ) -> th )";





  do {
    wph;
    wps;
    wch;
    wth;
    wi;
    wph;
    wps;
    wa;
    wch;
    wth;
    exp31.1;
    ex;
    ex;
  };

  return |- "( ph -> ( ps -> ( ch -> th ) ) )";
}
