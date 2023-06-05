include "biimpi.mm";
include "syl6.mm";

theorem syl6ib(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume syl6ib.1: |- "( ph -> ( ps -> ch ) )";
  assume syl6ib.2: |- "( ch <-> th )";





  do {
    wph;
    wps;
    wch;
    wth;
    syl6ib.1;
    wch;
    wth;
    syl6ib.2;
    biimpi;
    syl6;
  };

  return |- "( ph -> ( ps -> th ) )";
}
