include "wi.mm";
include "ax-2.mm";
include "syl.mm";

theorem a2d(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume a2d.1: |- "( ph -> ( ps -> ( ch -> th ) ) )";





  do {
    wph;
    wps;
    wch;
    wth;
    wi;
    wi;
    wps;
    wch;
    wi;
    wps;
    wth;
    wi;
    wi;
    a2d.1;
    wps;
    wch;
    wth;
    ax-2;
    syl;
  };

  return |- "( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) )";
}
