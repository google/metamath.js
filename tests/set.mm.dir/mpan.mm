include "a1i.mm";
include "mpancom.mm";

theorem mpan(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume mpan.1: |- "ph";
  assume mpan.2: |- "( ( ph /\\ ps ) -> ch )";





  do {
    wph;
    wps;
    wch;
    wph;
    wps;
    mpan.1;
    a1i;
    mpan.2;
    mpancom;
  };

  return |- "( ps -> ch )";
}
