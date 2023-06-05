include "wex.mm";
include "hbe1.mm";
include "nf5i.mm";

theorem nfe1(wph: wff ph, vx: setvar x) {





  do {
    wph;
    vx;
    wex;
    vx;
    wph;
    vx;
    hbe1;
    nf5i;
  };

  return |- "F/ x E. x ph";
}
