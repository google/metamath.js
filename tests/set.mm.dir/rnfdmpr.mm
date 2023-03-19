include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "wfn.mm"
include "crn.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "cab.mm"
include "fnrnfv.mm"
include "adantl.mm"
include "ciun.mm"
include "cun.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "abbidv.mm"
include "iunxprg.mm"
include "adantr.mm"
include "iunab.mm"
include "csn.mm"
include "df-sn.mm"
include "eqcomi.mm"
include "uneq12i.mm"
include "df-pr.mm"
include "eqtr4i.mm"
include "3eqtr3g.mm"
include "eqtrd.mm"
include "ex.mm"

theorem rnfdmpr
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vi: setvar i
  let vx: setvar x
  let vk: setvar k


  assert |- ( ( X e. V /\ Y e. W ) -> ( F Fn { X , Y } -> ran F = { ( F ` X ) , ( F ` Y ) } ) )

  proof
    cX
    cV
    wcel
    cY
    cW
    wcel
    wa
    #
    cF
    cX
    cY
    cpr
    #
    wfn
    #
    cF
    crn
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cpr
    #
    wceq
    @0
    @2
    wa
    #
    @3
    vx
    cv
    #
    vi
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vi
    @1
    wrex
    vx
    cab
    #
    @6
    @2
    @3
    @12
    wceq
    @0
    vi
    vx
    @1
    cF
    fnrnfv
    adantl
    @7
    vi
    @1
    @11
    vx
    cab
    #
    ciun
    #
    @8
    @4
    wceq
    #
    vx
    cab
    #
    @8
    @5
    wceq
    #
    vx
    cab
    #
    cun
    #
    @12
    @6
    @0
    @14
    @19
    wceq
    @2
    vi
    cX
    cY
    @13
    @16
    @18
    cV
    cW
    @9
    cX
    wceq
    #
    @11
    @15
    vx
    @20
    @10
    @4
    @8
    @9
    cX
    cF
    fveq2
    eqeq2d
    abbidv
    @9
    cY
    wceq
    #
    @11
    @17
    vx
    @21
    @10
    @5
    @8
    @9
    cY
    cF
    fveq2
    eqeq2d
    abbidv
    iunxprg
    adantr
    @11
    vi
    vx
    @1
    iunab
    @19
    @4
    csn
    #
    @5
    csn
    #
    cun
    @6
    @16
    @22
    @18
    @23
    @22
    @16
    vx
    @4
    df-sn
    eqcomi
    @23
    @18
    vx
    @5
    df-sn
    eqcomi
    uneq12i
    @4
    @5
    df-pr
    eqtr4i
    3eqtr3g
    eqtrd
    ex
end
