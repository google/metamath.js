include "wi.mm";
include "a1d.mm";
include "mpdd.mm";

theorem syld(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume syld.1: |- "( ph -> ( ps -> ch ) )";
  assume syld.2: |- "( ph -> ( ch -> th ) )";





  do {
    wph;
    wps;
    wch;
    wth;
    syld.1;
    wph;
    wch;
    wth;
    wi;
    wps;
    syld.2;
    a1d;
    mpdd;
  };

  return '|-' "( ph -> ( ps -> th ) )";
}
