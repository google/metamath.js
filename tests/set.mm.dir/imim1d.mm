include "idd.mm";
include "imim12d.mm";

theorem imim1d(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume imim1d.1: |- "( ph -> ( ps -> ch ) )";





  do {
    wph;
    wps;
    wch;
    wth;
    wth;
    imim1d.1;
    wph;
    wth;
    idd;
    imim12d;
  };

  return |- "( ph -> ( ( ch -> th ) -> ( ps -> th ) ) )";
}
