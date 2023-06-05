include "wi.mm";
include "a1d.mm";
include "a2d.mm";

theorem imim2d(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume imim2d.1: |- "( ph -> ( ps -> ch ) )";





  do {
    wph;
    wth;
    wps;
    wch;
    wph;
    wps;
    wch;
    wi;
    wth;
    imim2d.1;
    a1d;
    a2d;
  };

  return |- "( ph -> ( ( th -> ps ) -> ( th -> ch ) ) )";
}
