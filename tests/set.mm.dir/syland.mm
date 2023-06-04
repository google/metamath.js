include "wi.mm";
include "expd.mm";
include "syld.mm";
include "impd.mm";

theorem syland(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th, wta: 'wff' ta) {
  assume syland.1: |- "( ph -> ( ps -> ch ) )";
  assume syland.2: |- "( ph -> ( ( ch /\\ th ) -> ta ) )";





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
    wi;
    syland.1;
    wph;
    wch;
    wth;
    wta;
    syland.2;
    expd;
    syld;
    impd;
  };

  return '|-' "( ph -> ( ( ps /\\ th ) -> ta ) )";
}
