include "cv.mm";
include "cab.mm";
include "wcel.mm";
include "wb.mm";
include "nfab1.mm";
include "nfel2.mm";
include "nfv.mm";
include "nfbi.mm";
include "wceq.mm";
include "eleq1.mm";
include "bibi12d.mm";
include "abid.mm";
include "vtoclg1f.mm";

theorem elabg(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x, cA: 'class' A, cV: 'class' V) {
  assume elabg.1: |- "( x = A -> ( ph <-> ps ) )";

  disjoint ps x;
  disjoint A x;



  do {
    vx;
    cv;
    #;
    wph;
    vx;
    cab;
    #;
    wcel;
    #;
    wph;
    wb;
    cA;
    @1;
    wcel;
    #;
    wps;
    wb;
    vx;
    cA;
    cV;
    @3;
    wps;
    vx;
    vx;
    cA;
    @1;
    wph;
    vx;
    nfab1;
    nfel2;
    wps;
    vx;
    nfv;
    nfbi;
    @0;
    cA;
    wceq;
    @2;
    @3;
    wph;
    wps;
    @0;
    cA;
    @1;
    eleq1;
    elabg.1;
    bibi12d;
    wph;
    vx;
    abid;
    vtoclg1f;
  };

  return '|-' "( A e. V -> ( A e. { x | ph } <-> ps ) )";
}
