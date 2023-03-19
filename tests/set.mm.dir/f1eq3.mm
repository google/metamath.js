include "wceq.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "wf1.mm"
include "feq3.mm"
include "anbi1d.mm"
include "df-f1.mm"
include "3bitr4g.mm"

theorem f1eq3
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( A = B -> ( F : C -1-1-> A <-> F : C -1-1-> B ) )

  proof
    cA
    cB
    wceq
    #
    cC
    cA
    cF
    wf
    #
    cF
    ccnv
    wfun
    #
    wa
    cC
    cB
    cF
    wf
    #
    @2
    wa
    cC
    cA
    cF
    wf1
    cC
    cB
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
    feq3
    anbi1d
    cC
    cA
    cF
    df-f1
    cC
    cB
    cF
    df-f1
    3bitr4g
end
