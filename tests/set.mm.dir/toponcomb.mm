include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "cuni.mm"
include "ctopon.mm"
include "cfv.mm"
include "wi.mm"
include "toponcom.mm"
include "ex.mm"
include "adantl.mm"
include "adantr.mm"
include "impbid.mm"

theorem toponcomb
  let cJ: class J
  let cK: class K


  assert |- ( ( J e. Top /\ K e. Top ) -> ( J e. ( TopOn ` U. K ) <-> K e. ( TopOn ` U. J ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    wa
    cJ
    cK
    cuni
    ctopon
    cfv
    wcel
    #
    cK
    cJ
    cuni
    ctopon
    cfv
    wcel
    #
    @1
    @2
    @3
    wi
    @0
    @1
    @2
    @3
    cK
    cJ
    toponcom
    ex
    adantl
    @0
    @3
    @2
    wi
    @1
    @0
    @3
    @2
    cJ
    cK
    toponcom
    ex
    adantr
    impbid
end
