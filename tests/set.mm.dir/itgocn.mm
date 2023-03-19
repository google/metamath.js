include "citgo.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cc.mm"
include "wss.mm"
include "cpw.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cdgr.mm"
include "ccoe.mm"
include "c1.mm"
include "wa.mm"
include "cply.mm"
include "wrex.mm"
include "crab.mm"
include "df-itgo.mm"
include "dmmptss.mm"
include "sseli.mm"
include "cnex.mm"
include "elpw2.mm"
include "itgoval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "sylbi.mm"
include "syl.mm"
include "wn.mm"
include "c0.mm"
include "ndmfv.mm"
include "0ss.mm"
include "pm2.61i.mm"

theorem itgocn
  let cS: class S
  let vx: setvar x
  let vp: setvar p
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cT: class T


  assert |- ( IntgOver ` S ) C_ CC

  proof
    cS
    citgo
    cdm
    #
    wcel
    #
    cS
    citgo
    cfv
    #
    cc
    wss
    #
    @1
    cS
    cc
    cpw
    #
    wcel
    #
    @3
    @0
    @4
    cS
    va
    @4
    vb
    cv
    #
    vc
    cv
    #
    cfv
    cc0
    wceq
    @7
    cdgr
    cfv
    @7
    ccoe
    cfv
    cfv
    c1
    wceq
    wa
    vc
    va
    cv
    #
    cply
    cfv
    wrex
    vb
    cc
    crab
    citgo
    vb
    va
    vc
    df-itgo
    dmmptss
    sseli
    @5
    cS
    cc
    wss
    #
    @3
    cS
    cc
    cnex
    elpw2
    @9
    @2
    @8
    @6
    cfv
    cc0
    wceq
    @6
    cdgr
    cfv
    @6
    ccoe
    cfv
    cfv
    c1
    wceq
    wa
    vb
    cS
    cply
    cfv
    wrex
    #
    va
    cc
    crab
    cc
    va
    cS
    vb
    itgoval
    @10
    va
    cc
    ssrab2
    syl6eqss
    sylbi
    syl
    @1
    wn
    @2
    c0
    cc
    cS
    citgo
    ndmfv
    cc
    0ss
    syl6eqss
    pm2.61i
end
