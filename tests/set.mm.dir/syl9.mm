include "wi.mm";
include "a1i.mm";
include "syl5d.mm";

theorem syl9(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th, wta: 'wff' ta) {
  assume syl9.1: |- "( ph -> ( ps -> ch ) )";
  assume syl9.2: |- "( th -> ( ch -> ta ) )";





  do {
    wph;
    wps;
    wch;
    wth;
    wta;
    syl9.1;
    wth;
    wch;
    wta;
    wi;
    wi;
    wph;
    syl9.2;
    a1i;
    syl5d;
  };

  return '|-' "( ph -> ( th -> ( ps -> ta ) ) )";
}
