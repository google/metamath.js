include "wf1.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wf.mm"
include "cv.mm"
include "weq.mm"
include "wral.mm"
include "dff13.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "rspc2v.mm"
include "com12.mm"
include "adantl.mm"
include "sylbi.mm"
include "imp.mm"

theorem f1veqaeq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vc: setvar c
  let vd: setvar d


  assert |- ( ( F : A -1-1-> B /\ ( C e. A /\ D e. A ) ) -> ( ( F ` C ) = ( F ` D ) -> C = D ) )

  proof
    cA
    cB
    cF
    wf1
    #
    cC
    cA
    wcel
    cD
    cA
    wcel
    wa
    #
    cC
    cF
    cfv
    #
    cD
    cF
    cfv
    #
    wceq
    #
    cC
    cD
    wceq
    #
    wi
    #
    @0
    cA
    cB
    cF
    wf
    #
    vc
    cv
    #
    cF
    cfv
    #
    vd
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vc
    vd
    weq
    #
    wi
    #
    vd
    cA
    wral
    vc
    cA
    wral
    #
    wa
    @1
    @6
    wi
    #
    vc
    vd
    cA
    cB
    cF
    dff13
    @15
    @16
    @7
    @1
    @15
    @6
    @14
    @6
    @2
    @11
    wceq
    #
    cC
    @10
    wceq
    #
    wi
    vc
    vd
    cC
    cD
    cA
    cA
    @8
    cC
    wceq
    #
    @12
    @17
    @13
    @18
    @19
    @9
    @2
    @11
    @8
    cC
    cF
    fveq2
    eqeq1d
    @8
    cC
    @10
    eqeq1
    imbi12d
    @10
    cD
    wceq
    #
    @17
    @4
    @18
    @5
    @20
    @11
    @3
    @2
    @10
    cD
    cF
    fveq2
    eqeq2d
    @10
    cD
    cC
    eqeq2
    imbi12d
    rspc2v
    com12
    adantl
    sylbi
    imp
end
