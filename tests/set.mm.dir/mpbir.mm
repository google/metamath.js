include "biimpri.mm";
include "ax-mp.mm";

theorem mpbir(wph: wff ph, wps: wff ps) {
  assume mpbir.min: |- "ps";
  assume mpbir.maj: |- "( ph <-> ps )";





  do {
    wps;
    wph;
    mpbir.min;
    wph;
    wps;
    mpbir.maj;
    biimpri;
    ax-mp;
  };

  return |- "ph";
}
