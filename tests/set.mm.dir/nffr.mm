include "wfr.mm"
include "cv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "df-fr.mm"
include "nfcv.mm"
include "nfss.mm"
include "nfv.mm"
include "nfan.mm"
include "nfbr.mm"
include "nfn.mm"
include "nfral.mm"
include "nfrex.mm"
include "nfim.mm"
include "nfal.mm"
include "nfxfr.mm"

theorem nffr
  let vx: setvar x
  let cA: class A
  let cR: class R
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume nffr.r: |- F/_ x R
  assume nffr.a: |- F/_ x A


  assert |- F/ x R Fr A

  proof
    cA
    cR
    wfr
    va
    cv
    #
    cA
    wss
    #
    @0
    c0
    wne
    #
    wa
    #
    vc
    cv
    #
    vb
    cv
    #
    cR
    wbr
    #
    wn
    #
    vc
    @0
    wral
    #
    vb
    @0
    wrex
    #
    wi
    #
    va
    wal
    vx
    va
    vb
    vc
    cA
    cR
    df-fr
    @10
    vx
    va
    @3
    @9
    vx
    @1
    @2
    vx
    vx
    @0
    cA
    vx
    @0
    nfcv
    #
    nffr.a
    nfss
    @2
    vx
    nfv
    nfan
    @8
    vx
    vb
    @0
    @11
    @7
    vx
    vc
    @0
    @11
    @6
    vx
    vx
    @4
    @5
    cR
    vx
    @4
    nfcv
    nffr.r
    vx
    @5
    nfcv
    nfbr
    nfn
    nfral
    nfrex
    nfim
    nfal
    nfxfr
end
