include "wfun.mm"
include "cdm.mm"
include "wfn.mm"
include "wcel.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "funfn.mm"
include "fvco2.mm"
include "sylanb.mm"

theorem fvco
  let cA: class A
  let cF: class F
  let cG: class G


  assert |- ( ( Fun G /\ A e. dom G ) -> ( ( F o. G ) ` A ) = ( F ` ( G ` A ) ) )

  proof
    cG
    wfun
    cG
    cG
    cdm
    #
    wfn
    cA
    @0
    wcel
    cA
    cF
    cG
    ccom
    cfv
    cA
    cG
    cfv
    cF
    cfv
    wceq
    cG
    funfn
    @0
    cF
    cG
    cA
    fvco2
    sylanb
end
