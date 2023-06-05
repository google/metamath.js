include "com3r.mm";

theorem com3l(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume com3.1: |- "( ph -> ( ps -> ( ch -> th ) ) )";





  do {
    wch;
    wph;
    wps;
    wth;
    wph;
    wps;
    wch;
    wth;
    com3.1;
    com3r;
    com3r;
  };

  return |- "( ps -> ( ch -> ( ph -> th ) ) )";
}
