include "wa.mm";
include "wi.mm";
include "com3l.mm";
include "imp.mm";
include "com12.mm";

theorem impd(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume impd.1: |- "( ph -> ( ps -> ( ch -> th ) ) )";





  do {
    wps;
    wch;
    wa;
    wph;
    wth;
    wps;
    wch;
    wph;
    wth;
    wi;
    wph;
    wps;
    wch;
    wth;
    impd.1;
    com3l;
    imp;
    com12;
  };

  return |- "( ph -> ( ( ps /\\ ch ) -> th ) )";
}
