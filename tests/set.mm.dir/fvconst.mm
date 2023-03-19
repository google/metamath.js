include "csn.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "ffvelrn.mm"
include "elsni.mm"
include "syl.mm"

theorem fvconst
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A --> { B } /\ C e. A ) -> ( F ` C ) = B )

  proof
    cA
    cB
    csn
    #
    cF
    wf
    cC
    cA
    wcel
    wa
    cC
    cF
    cfv
    #
    @0
    wcel
    @1
    cB
    wceq
    cA
    @0
    cC
    cF
    ffvelrn
    @1
    cB
    elsni
    syl
end
