include "wi.mm";
include "imim2d.mm";
include "syl5d.mm";

theorem imim12d(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th, wta: wff ta) {
  assume imim12d.1: |- "( ph -> ( ps -> ch ) )";
  assume imim12d.2: |- "( ph -> ( th -> ta ) )";





  do {
    wph;
    wps;
    wch;
    wch;
    wth;
    wi;
    wta;
    imim12d.1;
    wph;
    wth;
    wta;
    wch;
    imim12d.2;
    imim2d;
    syl5d;
  };

  return |- "( ph -> ( ( ch -> th ) -> ( ps -> ta ) ) )";
}
