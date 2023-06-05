include "wi.mm";
include "wsb.mm";
include "sbi1.mm";
include "sbi2.mm";
include "impbii.mm";

theorem sbim(wph: wff ph, wps: wff ps, vx: setvar x, vy: setvar y) {





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
    sbi1;
    wph;
    wps;
    vx;
    vy;
    sbi2;
    impbii;
  };

  return |- "( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> [ y / x ] ps ) )";
}
