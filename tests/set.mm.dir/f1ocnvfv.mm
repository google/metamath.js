include "cfv.mm"
include "wceq.mm"
include "ccnv.mm"
include "wf1o.mm"
include "wcel.mm"
include "wa.mm"
include "fveq2.mm"
include "eqcoms.mm"
include "f1ocnvfv1.mm"
include "eqeq2d.mm"
include "syl5ib.mm"

theorem f1ocnvfv
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( F : A -1-1-onto-> B /\ C e. A ) -> ( ( F ` C ) = D -> ( `' F ` D ) = C ) )

  proof
    cC
    cF
    cfv
    #
    cD
    wceq
    cD
    cF
    ccnv
    #
    cfv
    #
    @0
    @1
    cfv
    #
    wceq
    #
    cA
    cB
    cF
    wf1o
    cC
    cA
    wcel
    wa
    #
    @2
    cC
    wceq
    @4
    cD
    @0
    cD
    @0
    @1
    fveq2
    eqcoms
    @5
    @3
    cC
    @2
    cA
    cB
    cC
    cF
    f1ocnvfv1
    eqeq2d
    syl5ib
end
