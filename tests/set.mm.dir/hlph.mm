include "chlo.mm"
include "wcel.mm"
include "ccbn.mm"
include "ccphlo.mm"
include "ishlo.mm"
include "simprbi.mm"

theorem hlph
  let cU: class U


  assert |- ( U e. CHilOLD -> U e. CPreHilOLD )

  proof
    cU
    chlo
    wcel
    cU
    ccbn
    wcel
    cU
    ccphlo
    wcel
    cU
    ishlo
    simprbi
end
