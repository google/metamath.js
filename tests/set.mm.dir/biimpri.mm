include "bicomi.mm";
include "biimpi.mm";

theorem biimpri(wph: 'wff' ph, wps: 'wff' ps) {
  assume biimpri.1: |- "( ph <-> ps )";





  do {
    wps;
    wph;
    wph;
    wps;
    biimpri.1;
    bicomi;
    biimpi;
  };

  return '|-' "( ps -> ph )";
}
