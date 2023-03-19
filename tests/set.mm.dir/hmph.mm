include "chmph.mm"
include "chmeo.mm"
include "ctop.mm"
include "cxp.mm"
include "df-hmph.mm"
include "hmeofn.mm"
include "brwitnlem.mm"

theorem hmph
  let cJ: class J
  let cK: class K


  assert |- ( J ~= K <-> ( J Homeo K ) =/= (/) )

  proof
    cJ
    cK
    chmph
    chmeo
    ctop
    ctop
    cxp
    df-hmph
    hmeofn
    brwitnlem
end
