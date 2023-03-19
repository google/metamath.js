include "ctop.mm"
include "wcel.mm"
include "cnei.mm"
include "cfv.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "wrex.mm"
include "simprr.mm"
include "neii2.mm"
include "sstr2.mm"
include "com12.mm"
include "anim2d.mm"
include "reximdv.mm"
include "mpan9.mm"
include "adantrr.mm"
include "wb.mm"
include "neiss2.mm"
include "isnei.mm"
include "syldan.mm"
include "adantr.mm"
include "mpbir2and.mm"

theorem ssnei2
  let cS: class S
  let cJ: class J
  let cM: class M
  let cN: class N
  let cX: class X
  let vg: setvar g
  let vh: setvar h
  let vp: setvar p
  let vv: setvar v
  let cP: class P
  assume neips.1: |- X = U. J


  assert |- ( ( ( J e. Top /\ N e. ( ( nei ` J ) ` S ) ) /\ ( N C_ M /\ M C_ X ) ) -> M e. ( ( nei ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    #
    cN
    cS
    cJ
    cnei
    cfv
    cfv
    #
    wcel
    #
    wa
    #
    cN
    cM
    wss
    #
    cM
    cX
    wss
    #
    wa
    #
    wa
    cM
    @1
    wcel
    #
    @5
    cS
    vg
    cv
    #
    wss
    #
    @8
    cM
    wss
    #
    wa
    #
    vg
    cJ
    wrex
    #
    @3
    @4
    @5
    simprr
    @3
    @4
    @12
    @5
    @3
    @9
    @8
    cN
    wss
    #
    wa
    #
    vg
    cJ
    wrex
    @4
    @12
    cS
    vg
    cJ
    cN
    neii2
    @4
    @14
    @11
    vg
    cJ
    @4
    @13
    @10
    @9
    @13
    @4
    @10
    @8
    cN
    cM
    sstr2
    com12
    anim2d
    reximdv
    mpan9
    adantrr
    @3
    @7
    @5
    @12
    wa
    wb
    #
    @6
    @0
    @2
    cS
    cX
    wss
    @15
    cS
    cJ
    cN
    cX
    neips.1
    neiss2
    cS
    vg
    cJ
    cM
    cX
    neips.1
    isnei
    syldan
    adantr
    mpbir2and
end
