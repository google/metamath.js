include "wn.mm";
include "ax-1.mm";
include "orrd.mm";

theorem olc(wph: wff ph, wps: wff ps) {





  do {
    wph;
    wps;
    wph;
    wph;
    wps;
    wn;
    ax-1;
    orrd;
  };

  return |- "( ph -> ( ps \\/ ph ) )";
}
