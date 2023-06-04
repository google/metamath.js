include "wa.mm";
include "ancom.mm";
include "syl5bi.mm";

theorem ancomsd(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume ancomsd.1: |- "( ph -> ( ( ps /\\ ch ) -> th ) )";





  do {
    wch;
    wps;
    wa;
    wps;
    wch;
    wa;
    wph;
    wth;
    wch;
    wps;
    ancom;
    ancomsd.1;
    syl5bi;
  };

  return '|-' "( ph -> ( ( ch /\\ ps ) -> th ) )";
}
