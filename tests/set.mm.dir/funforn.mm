include "wfun.mm"
include "cdm.mm"
include "wfn.mm"
include "crn.mm"
include "wfo.mm"
include "funfn.mm"
include "dffn4.mm"
include "bitri.mm"

theorem funforn
  let cA: class A


  assert |- ( Fun A <-> A : dom A -onto-> ran A )

  proof
    cA
    wfun
    cA
    cA
    cdm
    #
    wfn
    @0
    cA
    crn
    cA
    wfo
    cA
    funfn
    @0
    cA
    dffn4
    bitri
end
