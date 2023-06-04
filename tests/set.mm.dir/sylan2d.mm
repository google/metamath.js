include "ancomsd.mm";
include "syland.mm";

theorem sylan2d(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th, wta: 'wff' ta) {
  assume sylan2d.1: |- "( ph -> ( ps -> ch ) )";
  assume sylan2d.2: |- "( ph -> ( ( th /\\ ch ) -> ta ) )";





  do {
    wph;
    wps;
    wth;
    wta;
    wph;
    wps;
    wch;
    wth;
    wta;
    sylan2d.1;
    wph;
    wth;
    wch;
    wta;
    sylan2d.2;
    ancomsd;
    syland;
    ancomsd;
  };

  return '|-' "( ph -> ( ( th /\\ ps ) -> ta ) )";
}
