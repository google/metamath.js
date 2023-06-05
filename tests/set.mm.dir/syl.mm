include "wi.mm";
include "a1i.mm";
include "mpd.mm";

theorem syl(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume syl.1: |- "( ph -> ps )";
  assume syl.2: |- "( ps -> ch )";





  do {
    wph;
    wps;
    wch;
    syl.1;
    wps;
    wch;
    wi;
    wph;
    syl.2;
    a1i;
    mpd;
  };

  return |- "( ph -> ch )";
}
