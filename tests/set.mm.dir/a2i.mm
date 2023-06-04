include "wi.mm";
include "ax-2.mm";
include "ax-mp.mm";

theorem a2i(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume a2i.1: |- "( ph -> ( ps -> ch ) )";





  do {
    wph;
    wps;
    wch;
    wi;
    wi;
    wph;
    wps;
    wi;
    wph;
    wch;
    wi;
    wi;
    a2i.1;
    wph;
    wps;
    wch;
    ax-2;
    ax-mp;
  };

  return '|-' "( ( ph -> ps ) -> ( ph -> ch ) )";
}
