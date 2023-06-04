include "wi.mm";
include "imim2.mm";
include "syl6c.mm";

theorem syldd(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th, wta: 'wff' ta) {
  assume syldd.1: |- "( ph -> ( ps -> ( ch -> th ) ) )";
  assume syldd.2: |- "( ph -> ( ps -> ( th -> ta ) ) )";





  do {
    wph;
    wps;
    wth;
    wta;
    wi;
    wch;
    wth;
    wi;
    wch;
    wta;
    wi;
    syldd.2;
    syldd.1;
    wth;
    wta;
    wch;
    imim2;
    syl6c;
  };

  return '|-' "( ph -> ( ps -> ( ch -> ta ) ) )";
}
