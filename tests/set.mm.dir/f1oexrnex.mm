include "wf1o.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "ccnv.mm"
include "wf.mm"
include "simpl.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "fex.mm"
include "sylancom.mm"
include "wrel.mm"
include "wb.mm"
include "f1orel.mm"
include "adantr.mm"
include "relcnvexb.mm"
include "syl.mm"
include "mpbird.mm"

theorem f1oexrnex
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V


  assert |- ( ( F : A -1-1-onto-> B /\ B e. V ) -> F e. _V )

  proof
    cA
    cB
    cF
    wf1o
    #
    cB
    cV
    wcel
    #
    wa
    #
    cF
    cvv
    wcel
    #
    cF
    ccnv
    #
    cvv
    wcel
    #
    @0
    @1
    cB
    cA
    @4
    wf
    #
    @5
    @2
    @0
    cB
    cA
    @4
    wf1o
    @6
    @0
    @1
    simpl
    cA
    cB
    cF
    f1ocnv
    cB
    cA
    @4
    f1of
    3syl
    cB
    cA
    cV
    @4
    fex
    sylancom
    @2
    cF
    wrel
    #
    @3
    @5
    wb
    @0
    @7
    @1
    cA
    cB
    cF
    f1orel
    adantr
    cF
    relcnvexb
    syl
    mpbird
end
