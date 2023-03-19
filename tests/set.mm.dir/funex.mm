include "wfun.mm"
include "cdm.mm"
include "wfn.mm"
include "wcel.mm"
include "cvv.mm"
include "funfn.mm"
include "fnex.mm"
include "sylanb.mm"

theorem funex
  let cB: class B
  let cF: class F


  assert |- ( ( Fun F /\ dom F e. B ) -> F e. _V )

  proof
    cF
    wfun
    cF
    cF
    cdm
    #
    wfn
    @0
    cB
    wcel
    cF
    cvv
    wcel
    cF
    funfn
    @0
    cB
    cF
    fnex
    sylanb
end
