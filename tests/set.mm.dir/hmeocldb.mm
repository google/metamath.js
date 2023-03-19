include "ctop.mm"
include "wcel.mm"
include "chmeo.mm"
include "co.mm"
include "w3a.mm"
include "ccn.mm"
include "ccld.mm"
include "cfv.mm"
include "ccnv.mm"
include "cima.mm"
include "hmeocn.mm"
include "3ad2ant3.mm"
include "cnclima.mm"
include "sylan.mm"

theorem hmeocldb
  let cS: class S
  let cF: class F
  let cJ: class J
  let cK: class K


  assert |- ( ( ( J e. Top /\ K e. Top /\ F e. ( J Homeo K ) ) /\ S e. ( Clsd ` K ) ) -> ( `' F " S ) e. ( Clsd ` J ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    cF
    cJ
    cK
    chmeo
    co
    wcel
    #
    w3a
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cS
    cK
    ccld
    cfv
    wcel
    cF
    ccnv
    cS
    cima
    cJ
    ccld
    cfv
    wcel
    @2
    @0
    @3
    @1
    cF
    cJ
    cK
    hmeocn
    3ad2ant3
    cS
    cF
    cJ
    cK
    cnclima
    sylan
end
