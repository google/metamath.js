include "chlo.mm"
include "wcel.mm"
include "ccbn.mm"
include "ccphlo.mm"
include "ishlo.mm"
include "simplbi.mm"

theorem hlobn
  let cU: class U


  assert |- ( U e. CHilOLD -> U e. CBan )

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
    simplbi
end
