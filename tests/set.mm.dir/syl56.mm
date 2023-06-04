include "syl6.mm";
include "syl5.mm";

theorem syl56(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th, wta: 'wff' ta) {
  assume syl56.1: |- "( ph -> ps )";
  assume syl56.2: |- "( ch -> ( ps -> th ) )";
  assume syl56.3: |- "( th -> ta )";





  do {
    wph;
    wps;
    wch;
    wta;
    syl56.1;
    wch;
    wps;
    wth;
    wta;
    syl56.2;
    syl56.3;
    syl6;
    syl5;
  };

  return '|-' "( ch -> ( ph -> ta ) )";
}
