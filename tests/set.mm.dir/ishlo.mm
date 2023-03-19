include "ccbn.mm"
include "ccphlo.mm"
include "chlo.mm"
include "df-hlo.mm"
include "elin2.mm"

theorem ishlo
  let cU: class U


  assert |- ( U e. CHilOLD <-> ( U e. CBan /\ U e. CPreHilOLD ) )

  proof
    cU
    ccbn
    ccphlo
    chlo
    df-hlo
    elin2
end
