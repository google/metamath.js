include "wal.mm";
include "weq.mm";
include "biimpd.mm";
include "cbv3v.mm";
include "wi.mm";
include "biimprd.mm";
include "equcoms.mm";
include "impbii.mm";

theorem cbvalv1(wph: wff ph, wps: wff ps, vx: setvar x, vy: setvar y) {
  assume cbvalv1.nf1: |- "F/ y ph";
  assume cbvalv1.nf2: |- "F/ x ps";
  assume cbvalv1.1: |- "( x = y -> ( ph <-> ps ) )";

  disjoint x y;



  do {
    wph;
    vx;
    wal;
    wps;
    vy;
    wal;
    wph;
    wps;
    vx;
    vy;
    cbvalv1.nf1;
    cbvalv1.nf2;
    vx;
    vy;
    weq;
    #;
    wph;
    wps;
    cbvalv1.1;
    biimpd;
    cbv3v;
    wps;
    wph;
    vy;
    vx;
    cbvalv1.nf2;
    cbvalv1.nf1;
    wps;
    wph;
    wi;
    vx;
    vy;
    @0;
    wph;
    wps;
    cbvalv1.1;
    biimprd;
    equcoms;
    cbv3v;
    impbii;
  };

  return |- "( A. x ph <-> A. y ps )";
}
