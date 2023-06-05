include "wsb.mm";
include "nfs1v.mm";
include "nf5ri.mm";

theorem hbs1(wph: wff ph, vx: setvar x, vy: setvar y) {

  disjoint x y;



  do {
    wph;
    vx;
    vy;
    wsb;
    vx;
    wph;
    vx;
    vy;
    nfs1v;
    nf5ri;
  };

  return |- "( [ y / x ] ph -> A. x [ y / x ] ph )";
}
