include "id.mm";
include "syl2anc.mm";

theorem mpancom(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume mpancom.1: |- "( ps -> ph )";
  assume mpancom.2: |- "( ( ph /\\ ps ) -> ch )";





  do {
    wps;
    wph;
    wps;
    wch;
    mpancom.1;
    wps;
    id;
    mpancom.2;
    syl2anc;
  };

  return |- "( ps -> ch )";
}
