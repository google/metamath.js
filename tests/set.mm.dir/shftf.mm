include "wf.mm"
include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cshi.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "crab.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "ffn.mm"
include "shftfn.mm"
include "sylan.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "elrab.mm"
include "simpr.mm"
include "simpl.mm"
include "shftval.mm"
include "syl2an.mm"
include "ffvelrn.mm"
include "eqeltrd.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"

theorem shftf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume shftfval.1: |- F e. _V

  disjoint A x
  disjoint F x
  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C y
  assert |- ( ( F : B --> C /\ A e. CC ) -> ( F shift A ) : { x e. CC | ( x - A ) e. B } --> C )

  proof
    cB
    cC
    cF
    wf
    #
    cA
    cc
    wcel
    #
    wa
    #
    cF
    cA
    cshi
    co
    #
    vx
    cv
    #
    cA
    cmin
    co
    #
    cB
    wcel
    #
    vx
    cc
    crab
    #
    wfn
    #
    vy
    cv
    #
    @3
    cfv
    #
    cC
    wcel
    #
    vy
    @7
    wral
    @7
    cC
    @3
    wf
    @0
    cF
    cB
    wfn
    @1
    @8
    cB
    cC
    cF
    ffn
    vx
    cA
    cB
    cF
    shftfval.1
    shftfn
    sylan
    @2
    @11
    vy
    @7
    @9
    @7
    wcel
    @2
    @9
    cc
    wcel
    #
    @9
    cA
    cmin
    co
    #
    cB
    wcel
    #
    wa
    #
    @11
    @6
    @14
    vx
    @9
    cc
    @4
    @9
    wceq
    @5
    @13
    cB
    @4
    @9
    cA
    cmin
    oveq1
    eleq1d
    elrab
    @2
    @15
    wa
    @10
    @13
    cF
    cfv
    #
    cC
    @2
    @1
    @12
    @10
    @16
    wceq
    @15
    @0
    @1
    simpr
    @12
    @14
    simpl
    cA
    @9
    cF
    shftfval.1
    shftval
    syl2an
    @2
    @0
    @14
    @16
    cC
    wcel
    @15
    @0
    @1
    simpl
    @12
    @14
    simpr
    cB
    cC
    @13
    cF
    ffvelrn
    syl2an
    eqeltrd
    sylan2b
    ralrimiva
    vy
    @7
    cC
    @3
    ffnfv
    sylanbrc
end
