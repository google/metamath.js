include "syl5com.mm";
include "com12.mm";

theorem syl5(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume syl5.1: |- "( ph -> ps )";
  assume syl5.2: |- "( ch -> ( ps -> th ) )";





  do {
    wph;
    wch;
    wth;
    wph;
    wps;
    wch;
    wth;
    syl5.1;
    syl5.2;
    syl5com;
    com12;
  };

  return '|-' "( ch -> ( ph -> th ) )";
}
