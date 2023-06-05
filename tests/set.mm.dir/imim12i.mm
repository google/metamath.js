include "wi.mm";
include "imim2i.mm";
include "syl5.mm";

theorem imim12i(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume imim12i.1: |- "( ph -> ps )";
  assume imim12i.2: |- "( ch -> th )";





  do {
    wph;
    wps;
    wps;
    wch;
    wi;
    wth;
    imim12i.1;
    wch;
    wth;
    wps;
    imim12i.2;
    imim2i;
    syl5;
  };

  return |- "( ( ps -> ch ) -> ( ph -> th ) )";
}
