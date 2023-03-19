include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "cuni.mm"
include "cdm.mm"
include "cpw.mm"
include "crab.mm"
include "crn.mm"
include "cutop.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-utop.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "unieqd.mm"
include "dmeqd.mm"
include "ustbas2.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "pweqd.mm"
include "rexeqdv.mm"
include "ralbidv.mm"
include "rabeqbidv.mm"
include "elrnust.mm"
include "elfvex.mm"
include "pwexg.mm"
include "rabexg.mm"
include "3syl.mm"
include "fvmptd.mm"

theorem utopval
  let vx: setvar x
  let vv: setvar v
  let cU: class U
  let cX: class X
  let va: setvar a
  let vu: setvar u

  disjoint a v
  disjoint a x
  disjoint U a
  disjoint v x
  disjoint U v
  disjoint U x
  disjoint X a
  disjoint X x
  disjoint a u
  disjoint u v
  disjoint u x
  disjoint U u
  disjoint X u
  assert |- ( U e. ( UnifOn ` X ) -> ( unifTop ` U ) = { a e. ~P X | A. x e. a E. v e. U ( v " { x } ) C_ a } )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    vu
    cU
    vv
    cv
    vx
    cv
    csn
    cima
    va
    cv
    #
    wss
    #
    vv
    vu
    cv
    #
    wrex
    #
    vx
    @1
    wral
    #
    va
    @3
    cuni
    #
    cdm
    #
    cpw
    #
    crab
    #
    @2
    vv
    cU
    wrex
    #
    vx
    @1
    wral
    #
    va
    cX
    cpw
    #
    crab
    #
    cust
    crn
    cuni
    #
    cutop
    cvv
    cutop
    vu
    @14
    @9
    cmpt
    wceq
    @0
    vx
    vv
    vu
    va
    df-utop
    a1i
    @0
    @3
    cU
    wceq
    #
    wa
    #
    @5
    @11
    va
    @8
    @12
    @16
    @7
    cX
    @16
    @7
    cU
    cuni
    #
    cdm
    #
    cX
    @16
    @6
    @17
    @16
    @3
    cU
    @0
    @15
    simpr
    #
    unieqd
    dmeqd
    @0
    cX
    @18
    wceq
    @15
    cU
    cX
    ustbas2
    adantr
    eqtr4d
    pweqd
    @16
    @4
    @10
    vx
    @1
    @16
    @2
    vv
    @3
    cU
    @19
    rexeqdv
    ralbidv
    rabeqbidv
    cU
    cX
    elrnust
    @0
    cX
    cvv
    wcel
    @12
    cvv
    wcel
    @13
    cvv
    wcel
    cU
    cX
    cust
    elfvex
    cX
    cvv
    pwexg
    @11
    va
    @12
    cvv
    rabexg
    3syl
    fvmptd
end
