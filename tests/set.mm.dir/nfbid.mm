include "wb.mm";
include "wi.mm";
include "wa.mm";
include "dfbi2.mm";
include "nfimd.mm";
include "nfand.mm";
include "nfxfrd.mm";

theorem nfbid(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, vx: 'setvar' x) {
  assume nfbid.1: |- "( ph -> F/ x ps )";
  assume nfbid.2: |- "( ph -> F/ x ch )";





  do {
    wps;
    wch;
    wb;
    wps;
    wch;
    wi;
    #;
    wch;
    wps;
    wi;
    #;
    wa;
    wph;
    vx;
    wps;
    wch;
    dfbi2;
    wph;
    @0;
    @1;
    vx;
    wph;
    wps;
    wch;
    vx;
    nfbid.1;
    nfbid.2;
    nfimd;
    wph;
    wch;
    wps;
    vx;
    nfbid.2;
    nfbid.1;
    nfimd;
    nfand;
    nfxfrd;
  };

  return '|-' "( ph -> F/ x ( ps <-> ch ) )";
}
