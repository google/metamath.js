include "wa.mm";
include "wn.mm";
include "wi.mm";
include "df-an.mm";
include "nfnd.mm";
include "nfimd.mm";
include "nfxfrd.mm";

theorem nfand(wph: wff ph, wps: wff ps, wch: wff ch, vx: setvar x) {
  assume nfand.1: |- "( ph -> F/ x ps )";
  assume nfand.2: |- "( ph -> F/ x ch )";





  do {
    wps;
    wch;
    wa;
    wps;
    wch;
    wn;
    #;
    wi;
    #;
    wn;
    wph;
    vx;
    wps;
    wch;
    df-an;
    wph;
    @1;
    vx;
    wph;
    wps;
    @0;
    vx;
    nfand.1;
    wph;
    wch;
    vx;
    nfand.2;
    nfnd;
    nfimd;
    nfnd;
    nfxfrd;
  };

  return |- "( ph -> F/ x ( ps /\\ ch ) )";
}
