include "wal.mm";
include "ax-gen.mm";
include "mpbir.mm";

theorem mpgbir(wph: wff ph, wps: wff ps, vx: setvar x) {
  assume mpgbir.1: |- "( ph <-> A. x ps )";
  assume mpgbir.2: |- "ps";





  do {
    wph;
    wps;
    vx;
    wal;
    wps;
    vx;
    mpgbir.2;
    ax-gen;
    mpgbir.1;
    mpbir;
  };

  return |- "ph";
}
