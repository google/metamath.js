include "cab.mm";
include "wss.mm";
include "cv.mm";
include "wcel.mm";
include "wi.mm";
include "wal.mm";
include "nfab1.mm";
include "dfss2f.mm";
include "abid.mm";
include "imbi12i.mm";
include "albii.mm";
include "bitri.mm";

theorem ss2ab(wph: wff ph, wps: wff ps, vx: setvar x) {





  do {
    wph;
    vx;
    cab;
    #;
    wps;
    vx;
    cab;
    #;
    wss;
    vx;
    cv;
    #;
    @0;
    wcel;
    #;
    @2;
    @1;
    wcel;
    #;
    wi;
    #;
    vx;
    wal;
    wph;
    wps;
    wi;
    #;
    vx;
    wal;
    vx;
    @0;
    @1;
    wph;
    vx;
    nfab1;
    wps;
    vx;
    nfab1;
    dfss2f;
    @5;
    @6;
    vx;
    @3;
    wph;
    @4;
    wps;
    wph;
    vx;
    abid;
    wps;
    vx;
    abid;
    imbi12i;
    albii;
    bitri;
  };

  return |- "( { x | ph } C_ { x | ps } <-> A. x ( ph -> ps ) )";
}
