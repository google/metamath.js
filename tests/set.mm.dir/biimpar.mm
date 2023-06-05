include "biimprd.mm";
include "imp.mm";

theorem biimpar(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume biimpa.1: |- "( ph -> ( ps <-> ch ) )";





  do {
    wph;
    wch;
    wps;
    wph;
    wps;
    wch;
    biimpa.1;
    biimprd;
    imp;
  };

  return |- "( ( ph /\\ ch ) -> ps )";
}
