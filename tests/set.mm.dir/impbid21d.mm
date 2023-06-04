include "wi.mm";
include "a1i.mm";
include "a1d.mm";
include "impbidd.mm";

theorem impbid21d(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume impbid21d.1: |- "( ps -> ( ch -> th ) )";
  assume impbid21d.2: |- "( ph -> ( th -> ch ) )";





  do {
    wph;
    wps;
    wch;
    wth;
    wps;
    wch;
    wth;
    wi;
    wi;
    wph;
    impbid21d.1;
    a1i;
    wph;
    wth;
    wch;
    wi;
    wps;
    impbid21d.2;
    a1d;
    impbidd;
  };

  return '|-' "( ph -> ( ps -> ( ch <-> th ) ) )";
}
