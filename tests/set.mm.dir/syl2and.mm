include "sylan2d.mm";
include "syland.mm";

theorem syl2and(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th, wta: 'wff' ta, wet: 'wff' et) {
  assume syl2and.1: |- "( ph -> ( ps -> ch ) )";
  assume syl2and.2: |- "( ph -> ( th -> ta ) )";
  assume syl2and.3: |- "( ph -> ( ( ch /\\ ta ) -> et ) )";





  do {
    wph;
    wps;
    wch;
    wth;
    wet;
    syl2and.1;
    wph;
    wth;
    wta;
    wch;
    wet;
    syl2and.2;
    syl2and.3;
    sylan2d;
    syland;
  };

  return '|-' "( ph -> ( ( ps /\\ th ) -> et ) )";
}
