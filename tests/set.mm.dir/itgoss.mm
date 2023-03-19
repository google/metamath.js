include "wss.mm"
include "cc.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cdgr.mm"
include "ccoe.mm"
include "c1.mm"
include "cply.mm"
include "wrex.mm"
include "crab.mm"
include "citgo.mm"
include "wi.mm"
include "wral.mm"
include "plyss.mm"
include "ssrexv.mm"
include "syl.mm"
include "ralrimivw.mm"
include "ss2rab.mm"
include "sylibr.mm"
include "sstr.mm"
include "itgoval.mm"
include "adantl.mm"
include "3sstr4d.mm"

theorem itgoss
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vp: setvar p
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( S C_ T /\ T C_ CC ) -> ( IntgOver ` S ) C_ ( IntgOver ` T ) )

  proof
    cS
    cT
    wss
    #
    cT
    cc
    wss
    #
    wa
    #
    va
    cv
    vb
    cv
    #
    cfv
    cc0
    wceq
    @3
    cdgr
    cfv
    @3
    ccoe
    cfv
    cfv
    c1
    wceq
    wa
    #
    vb
    cS
    cply
    cfv
    #
    wrex
    #
    va
    cc
    crab
    #
    @4
    vb
    cT
    cply
    cfv
    #
    wrex
    #
    va
    cc
    crab
    #
    cS
    citgo
    cfv
    #
    cT
    citgo
    cfv
    #
    @2
    @6
    @9
    wi
    #
    va
    cc
    wral
    @7
    @10
    wss
    @2
    @13
    va
    cc
    @2
    @5
    @8
    wss
    @13
    cS
    cT
    plyss
    @4
    vb
    @5
    @8
    ssrexv
    syl
    ralrimivw
    @6
    @9
    va
    cc
    ss2rab
    sylibr
    @2
    cS
    cc
    wss
    @11
    @7
    wceq
    cS
    cT
    cc
    sstr
    va
    cS
    vb
    itgoval
    syl
    @1
    @12
    @10
    wceq
    @0
    va
    cT
    vb
    itgoval
    adantl
    3sstr4d
end
