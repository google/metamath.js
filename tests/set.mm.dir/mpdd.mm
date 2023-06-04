include "wi.mm";
include "a2d.mm";
include "mpd.mm";

theorem mpdd(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume mpdd.1: |- "( ph -> ( ps -> ch ) )";
  assume mpdd.2: |- "( ph -> ( ps -> ( ch -> th ) ) )";





  do {
    wph;
    wps;
    wch;
    wi;
    wps;
    wth;
    wi;
    mpdd.1;
    wph;
    wps;
    wch;
    wth;
    mpdd.2;
    a2d;
    mpd;
  };

  return '|-' "( ph -> ( ps -> th ) )";
}
