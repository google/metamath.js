include "wal.mm";
include "ax-gen.mm";
include "ax-mp.mm";

theorem mpg(wph: wff ph, wps: wff ps, vx: setvar x) {
  assume mpg.1: |- "( A. x ph -> ps )";
  assume mpg.2: |- "ph";





  do {
    wph;
    vx;
    wal;
    wps;
    wph;
    vx;
    mpg.2;
    ax-gen;
    mpg.1;
    ax-mp;
  };

  return |- "ps";
}
