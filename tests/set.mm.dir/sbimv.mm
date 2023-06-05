include "wi.mm";
include "wsb.mm";
include "sbi1v.mm";
include "sbi2v.mm";
include "impbii.mm";

theorem sbimv(wph: wff ph, wps: wff ps, vx: setvar x, vy: setvar y) {

  disjoint x y;



  do {
    wph;
    wps;
    wi;
    vx;
    vy;
    wsb;
    wph;
    vx;
    vy;
    wsb;
    wps;
    vx;
    vy;
    wsb;
    wi;
    wph;
    wps;
    vx;
    vy;
    sbi1v;
    wph;
    wps;
    vx;
    vy;
    sbi2v;
    impbii;
  };

  return |- "( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> [ y / x ] ps ) )";
}
