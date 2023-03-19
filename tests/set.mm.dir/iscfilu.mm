include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "ccfilu.mm"
include "cuni.mm"
include "cdm.mm"
include "cfbas.mm"
include "cv.mm"
include "cxp.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "crab.mm"
include "crn.mm"
include "wceq.mm"
include "elrnust.mm"
include "unieq.mm"
include "dmeqd.mm"
include "fveq2d.mm"
include "raleq.mm"
include "rabeqbidv.mm"
include "df-cfilu.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eleq2d.mm"
include "rexeq.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "ustbas2.mm"
include "anbi1d.mm"
include "bitr4d.mm"

theorem iscfilu
  let vv: setvar v
  let cU: class U
  let cF: class F
  let cX: class X
  let va: setvar a
  let vf: setvar f
  let vu: setvar u

  disjoint a v
  disjoint F a
  disjoint F v
  disjoint U v
  disjoint a f
  disjoint a u
  disjoint f u
  disjoint f v
  disjoint u v
  disjoint F f
  disjoint U f
  disjoint U u
  assert |- ( U e. ( UnifOn ` X ) -> ( F e. ( CauFilU ` U ) <-> ( F e. ( fBas ` X ) /\ A. v e. U E. a e. F ( a X. a ) C_ v ) ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cF
    cU
    ccfilu
    cfv
    #
    wcel
    #
    cF
    cU
    cuni
    #
    cdm
    #
    cfbas
    cfv
    #
    wcel
    #
    va
    cv
    #
    @7
    cxp
    vv
    cv
    wss
    #
    va
    cF
    wrex
    #
    vv
    cU
    wral
    #
    wa
    #
    cF
    cX
    cfbas
    cfv
    #
    wcel
    #
    @10
    wa
    @0
    @2
    cF
    @8
    va
    vf
    cv
    #
    wrex
    #
    vv
    cU
    wral
    #
    vf
    @5
    crab
    #
    wcel
    @11
    @0
    @1
    @17
    cF
    @0
    cU
    cust
    crn
    cuni
    #
    wcel
    @1
    @17
    wceq
    cU
    cX
    elrnust
    vu
    cU
    @15
    vv
    vu
    cv
    #
    wral
    #
    vf
    @19
    cuni
    #
    cdm
    #
    cfbas
    cfv
    #
    crab
    @17
    @18
    ccfilu
    @19
    cU
    wceq
    #
    @20
    @16
    vf
    @23
    @5
    @24
    @22
    @4
    cfbas
    @24
    @21
    @3
    @19
    cU
    unieq
    dmeqd
    fveq2d
    @15
    vv
    @19
    cU
    raleq
    rabeqbidv
    vv
    vu
    vf
    va
    df-cfilu
    @16
    vf
    @5
    @4
    cfbas
    fvex
    rabex
    fvmpt
    syl
    eleq2d
    @16
    @10
    vf
    cF
    @5
    @14
    cF
    wceq
    @15
    @9
    vv
    cU
    @8
    va
    @14
    cF
    rexeq
    ralbidv
    elrab
    syl6bb
    @0
    @13
    @6
    @10
    @0
    @12
    @5
    cF
    @0
    cX
    @4
    cfbas
    cU
    cX
    ustbas2
    fveq2d
    eleq2d
    anbi1d
    bitr4d
end
