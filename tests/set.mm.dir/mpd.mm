include "wi.mm";
include "a2i.mm";
include "ax-mp.mm";

theorem mpd(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume mpd.1: |- "( ph -> ps )";
  assume mpd.2: |- "( ph -> ( ps -> ch ) )";





  do {
    wph;
    wps;
    wi;
    wph;
    wch;
    wi;
    mpd.1;
    wph;
    wps;
    wch;
    mpd.2;
    a2i;
    ax-mp;
  };

  return '|-' "( ph -> ch )";
}
