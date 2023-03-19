include "wfun.mm"
include "wrel.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "wss.mm"
include "wa.mm"
include "df-fun.mm"
include "nfrel.mm"
include "nfcnv.mm"
include "nfco.mm"
include "nfcv.mm"
include "nfss.mm"
include "nfan.mm"
include "nfxfr.mm"

theorem nffun
  let vx: setvar x
  let cF: class F
  assume nffun.1: |- F/_ x F


  assert |- F/ x Fun F

  proof
    cF
    wfun
    cF
    wrel
    #
    cF
    cF
    ccnv
    #
    ccom
    #
    cid
    wss
    #
    wa
    vx
    cF
    df-fun
    @0
    @3
    vx
    vx
    cF
    nffun.1
    nfrel
    vx
    @2
    cid
    vx
    cF
    @1
    nffun.1
    vx
    cF
    nffun.1
    nfcnv
    nfco
    vx
    cid
    nfcv
    nfss
    nfan
    nfxfr
end
