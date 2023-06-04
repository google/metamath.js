include "syl6.mm";
include "com12.mm";

theorem syl6com(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume syl6com.1: |- "( ph -> ( ps -> ch ) )";
  assume syl6com.2: |- "( ch -> th )";





  do {
    wph;
    wps;
    wth;
    wph;
    wps;
    wch;
    wth;
    syl6com.1;
    syl6com.2;
    syl6;
    com12;
  };

  return '|-' "( ps -> ( ph -> th ) )";
}
