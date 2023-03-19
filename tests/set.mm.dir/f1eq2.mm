include "wceq.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "wf1.mm"
include "feq2.mm"
include "anbi1d.mm"
include "df-f1.mm"
include "3bitr4g.mm"

theorem f1eq2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( A = B -> ( F : A -1-1-> C <-> F : B -1-1-> C ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cC
    cF
    wf
    #
    cF
    ccnv
    wfun
    #
    wa
    cB
    cC
    cF
    wf
    #
    @2
    wa
    cA
    cC
    cF
    wf1
    cB
    cC
    cF
    wf1
    @0
    @1
    @3
    @2
    cA
    cB
    cC
    cF
    feq2
    anbi1d
    cA
    cC
    cF
    df-f1
    cB
    cC
    cF
    df-f1
    3bitr4g
end
