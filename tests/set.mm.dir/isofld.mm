include "cfield.mm"
include "corng.mm"
include "cofld.mm"
include "df-ofld.mm"
include "elin2.mm"

theorem isofld
  let cF: class F


  assert |- ( F e. oField <-> ( F e. Field /\ F e. oRing ) )

  proof
    cF
    cfield
    corng
    cofld
    df-ofld
    elin2
end
