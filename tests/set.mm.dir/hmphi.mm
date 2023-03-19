include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "chmph.mm"
include "wbr.mm"
include "ne0i.mm"
include "hmph.mm"
include "sylibr.mm"

theorem hmphi
  let cF: class F
  let cJ: class J
  let cK: class K


  assert |- ( F e. ( J Homeo K ) -> J ~= K )

  proof
    cF
    cJ
    cK
    chmeo
    co
    #
    wcel
    @0
    c0
    wne
    cJ
    cK
    chmph
    wbr
    @0
    cF
    ne0i
    cJ
    cK
    hmph
    sylibr
end
