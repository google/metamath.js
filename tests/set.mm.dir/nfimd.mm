include "wi.mm";
include "wex.mm";
include "wal.mm";
include "19.35.mm";
include "biimpi.mm";
include "nfrd.mm";
include "imim12d.mm";
include "19.38.mm";
include "syl56.mm";
include "nfd.mm";

theorem nfimd(wph: wff ph, wps: wff ps, wch: wff ch, vx: setvar x) {
  assume nfimd.1: |- "( ph -> F/ x ps )";
  assume nfimd.2: |- "( ph -> F/ x ch )";





  do {
    wph;
    wps;
    wch;
    wi;
    #;
    vx;
    @0;
    vx;
    wex;
    #;
    wps;
    vx;
    wal;
    #;
    wch;
    vx;
    wex;
    #;
    wi;
    #;
    wph;
    wps;
    vx;
    wex;
    #;
    wch;
    vx;
    wal;
    #;
    wi;
    @0;
    vx;
    wal;
    @1;
    @4;
    wps;
    wch;
    vx;
    19.35;
    biimpi;
    wph;
    @5;
    @2;
    @3;
    @6;
    wph;
    wps;
    vx;
    nfimd.1;
    nfrd;
    wph;
    wch;
    vx;
    nfimd.2;
    nfrd;
    imim12d;
    wps;
    wch;
    vx;
    19.38;
    syl56;
    nfd;
  };

  return |- "( ph -> F/ x ( ps -> ch ) )";
}
