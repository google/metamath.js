include "cnv.mm"
include "wcel.mm"
include "chmo.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cdm.mm"
include "crab.mm"
include "caj.mm"
include "co.mm"
include "oveq12.mm"
include "anidms.mm"
include "syl6eqr.mm"
include "dmeqd.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "rabeqbidv.mm"
include "df-hmo.mm"
include "cvv.mm"
include "ovex.mm"
include "eqeltri.mm"
include "dmex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl5eq.mm"

theorem hmoval
  let vt: setvar t
  let cA: class A
  let cU: class U
  let cH: class H
  let vu: setvar u
  let cT: class T
  assume hmoval.8: |- H = ( HmOp ` U )
  assume hmoval.9: |- A = ( U adj U )

  disjoint A t
  disjoint U t
  disjoint t u
  disjoint A u
  disjoint T t
  disjoint U u
  assert |- ( U e. NrmCVec -> H = { t e. dom A | ( A ` t ) = t } )

  proof
    cU
    cnv
    wcel
    cH
    cU
    chmo
    cfv
    vt
    cv
    #
    cA
    cfv
    #
    @0
    wceq
    #
    vt
    cA
    cdm
    #
    crab
    #
    hmoval.8
    vu
    cU
    @0
    vu
    cv
    #
    @5
    caj
    co
    #
    cfv
    #
    @0
    wceq
    #
    vt
    @6
    cdm
    #
    crab
    @4
    cnv
    chmo
    @5
    cU
    wceq
    #
    @8
    @2
    vt
    @9
    @3
    @10
    @6
    cA
    @10
    @6
    cU
    cU
    caj
    co
    #
    cA
    @10
    @6
    @11
    wceq
    @5
    cU
    @5
    cU
    caj
    oveq12
    anidms
    hmoval.9
    syl6eqr
    #
    dmeqd
    @10
    @7
    @1
    @0
    @10
    @0
    @6
    cA
    @12
    fveq1d
    eqeq1d
    rabeqbidv
    vu
    vt
    df-hmo
    @2
    vt
    @3
    cA
    cA
    @11
    cvv
    hmoval.9
    cU
    cU
    caj
    ovex
    eqeltri
    dmex
    rabex
    fvmpt
    syl5eq
end
