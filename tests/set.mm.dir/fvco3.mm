include "wf.mm"
include "wfn.mm"
include "wcel.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "ffn.mm"
include "fvco2.mm"
include "sylan.mm"

theorem fvco3
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G


  assert |- ( ( G : A --> B /\ C e. A ) -> ( ( F o. G ) ` C ) = ( F ` ( G ` C ) ) )

  proof
    cA
    cB
    cG
    wf
    cG
    cA
    wfn
    cC
    cA
    wcel
    cC
    cF
    cG
    ccom
    cfv
    cC
    cG
    cfv
    cF
    cfv
    wceq
    cA
    cB
    cG
    ffn
    cA
    cF
    cG
    cC
    fvco2
    sylan
end
