include "biimpi.mm";
include "ax-mp.mm";

theorem mpbi(wph: wff ph, wps: wff ps) {
  assume mpbi.min: |- "ph";
  assume mpbi.maj: |- "( ph <-> ps )";





  do {
    wph;
    wps;
    mpbi.min;
    wph;
    wps;
    mpbi.maj;
    biimpi;
    ax-mp;
  };

  return |- "ps";
}
