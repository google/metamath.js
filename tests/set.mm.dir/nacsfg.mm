include "wcel.mm"
include "cnacs.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "cacs.mm"
include "isnacs.mm"
include "simprbi.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "sylan2.mm"
include "ancoms.mm"

theorem nacsfg
  let cC: class C
  let cS: class S
  let vg: setvar g
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vs: setvar s
  let vx: setvar x
  assume isnacs.f: |- F = ( mrCls ` C )

  disjoint C g
  disjoint F g
  disjoint S g
  disjoint X g
  disjoint C c
  disjoint C s
  disjoint c g
  disjoint c s
  disjoint g s
  disjoint F c
  disjoint F s
  disjoint S s
  disjoint X c
  disjoint X s
  disjoint X x
  disjoint c x
  disjoint g x
  disjoint s x
  assert |- ( ( C e. ( NoeACS ` X ) /\ S e. C ) -> E. g e. ( ~P X i^i Fin ) S = ( F ` g ) )

  proof
    cS
    cC
    wcel
    #
    cC
    cX
    cnacs
    cfv
    wcel
    #
    cS
    vg
    cv
    cF
    cfv
    #
    wceq
    #
    vg
    cX
    cpw
    cfn
    cin
    #
    wrex
    #
    @1
    @0
    vs
    cv
    #
    @2
    wceq
    #
    vg
    @4
    wrex
    #
    vs
    cC
    wral
    #
    @5
    @1
    cC
    cX
    cacs
    cfv
    wcel
    @9
    cC
    vg
    cF
    cX
    vs
    isnacs.f
    isnacs
    simprbi
    @8
    @5
    vs
    cS
    cC
    @6
    cS
    wceq
    @7
    @3
    vg
    @4
    @6
    cS
    @2
    eqeq1
    rexbidv
    rspcva
    sylan2
    ancoms
end
