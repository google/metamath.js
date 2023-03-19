include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "cvv.mm"
include "crn.mm"
include "funex.mm"
include "ex.mm"
include "rnexg.mm"
include "syl6com.mm"

theorem funrnex
  let cB: class B
  let cF: class F


  assert |- ( dom F e. B -> ( Fun F -> ran F e. _V ) )

  proof
    cF
    wfun
    #
    cF
    cdm
    cB
    wcel
    #
    cF
    cvv
    wcel
    #
    cF
    crn
    cvv
    wcel
    @0
    @1
    @2
    cB
    cF
    funex
    ex
    cF
    cvv
    rnexg
    syl6com
end
