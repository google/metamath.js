include "syld.mm";
include "com12.mm";

theorem syldc(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume syld.1: |- "( ph -> ( ps -> ch ) )";
  assume syld.2: |- "( ph -> ( ch -> th ) )";





  do {
    wph;
    wps;
    wth;
    wph;
    wps;
    wch;
    wth;
    syld.1;
    syld.2;
    syld;
    com12;
  };

  return |- "( ps -> ( ph -> th ) )";
}
