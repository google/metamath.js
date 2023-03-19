include "wf1.mm"
include "crn.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wf1o.mm"
include "f1f1orn.mm"
include "f1ocnv.mm"
include "f1of1.mm"
include "f1veqaeq.mm"
include "ex.mm"
include "4syl.mm"
include "imp.mm"

theorem f1ocnvfvrneq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( F : A -1-1-> B /\ ( C e. ran F /\ D e. ran F ) ) -> ( ( `' F ` C ) = ( `' F ` D ) -> C = D ) )

  proof
    cA
    cB
    cF
    wf1
    #
    cC
    cF
    crn
    #
    wcel
    cD
    @1
    wcel
    wa
    #
    cC
    cF
    ccnv
    #
    cfv
    cD
    @3
    cfv
    wceq
    cC
    cD
    wceq
    wi
    #
    @0
    cA
    @1
    cF
    wf1o
    @1
    cA
    @3
    wf1o
    @1
    cA
    @3
    wf1
    #
    @2
    @4
    wi
    cA
    cB
    cF
    f1f1orn
    cA
    @1
    cF
    f1ocnv
    @1
    cA
    @3
    f1of1
    @5
    @2
    @4
    @1
    cA
    cC
    cD
    @3
    f1veqaeq
    ex
    4syl
    imp
end
