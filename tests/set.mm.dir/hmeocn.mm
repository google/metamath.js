include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "ccn.mm"
include "ccnv.mm"
include "ishmeo.mm"
include "simplbi.mm"

theorem hmeocn
  let cF: class F
  let cJ: class J
  let cK: class K


  assert |- ( F e. ( J Homeo K ) -> F e. ( J Cn K ) )

  proof
    cF
    cJ
    cK
    chmeo
    co
    wcel
    cF
    cJ
    cK
    ccn
    co
    wcel
    cF
    ccnv
    cK
    cJ
    ccn
    co
    wcel
    cF
    cJ
    cK
    ishmeo
    simplbi
end
