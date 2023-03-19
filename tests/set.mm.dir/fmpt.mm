include "wcel.mm"
include "wral.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "fnmpt.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "rnmpt.mm"
include "wa.mm"
include "r19.29.mm"
include "eleq1.mm"
include "biimparc.mm"
include "rexlimivw.mm"
include "syl.mm"
include "ex.mm"
include "abssdv.mm"
include "syl5eqss.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "crab.mm"
include "ccnv.mm"
include "cima.mm"
include "mptpreima.mm"
include "fimacnv.mm"
include "syl5reqr.mm"
include "rabid2.mm"
include "sylib.mm"
include "impbii.mm"

theorem fmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  assume fmpt.1: |- F = ( x e. A |-> C )

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint F y
  disjoint F z
  assert |- ( A. x e. A C e. B <-> F : A --> B )

  proof
    cC
    cB
    wcel
    #
    vx
    cA
    wral
    #
    cA
    cB
    cF
    wf
    #
    @1
    cF
    cA
    wfn
    cF
    crn
    #
    cB
    wss
    @2
    vx
    cA
    cC
    cF
    cB
    fmpt.1
    fnmpt
    @1
    @3
    vy
    cv
    #
    cC
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    cB
    vx
    vy
    cA
    cC
    cF
    fmpt.1
    rnmpt
    @1
    @6
    vy
    cB
    @1
    @6
    @4
    cB
    wcel
    #
    @1
    @6
    wa
    @0
    @5
    wa
    #
    vx
    cA
    wrex
    @7
    @0
    @5
    vx
    cA
    r19.29
    @8
    @7
    vx
    cA
    @5
    @7
    @0
    @4
    cC
    cB
    eleq1
    biimparc
    rexlimivw
    syl
    ex
    abssdv
    syl5eqss
    cA
    cB
    cF
    df-f
    sylanbrc
    @2
    cA
    @0
    vx
    cA
    crab
    #
    wceq
    @1
    @2
    @9
    cF
    ccnv
    cB
    cima
    cA
    vx
    cA
    cC
    cB
    cF
    fmpt.1
    mptpreima
    cA
    cB
    cF
    fimacnv
    syl5reqr
    @0
    vx
    cA
    rabid2
    sylib
    impbii
end
