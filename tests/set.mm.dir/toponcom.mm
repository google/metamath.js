include "ctop.mm"
include "wcel.mm"
include "cuni.mm"
include "ctopon.mm"
include "cfv.mm"
include "wa.mm"
include "wceq.mm"
include "toponuni.mm"
include "eqcomd.mm"
include "anim2i.mm"
include "istopon.mm"
include "sylibr.mm"

theorem toponcom
  let cJ: class J
  let cK: class K


  assert |- ( ( J e. Top /\ K e. ( TopOn ` U. J ) ) -> J e. ( TopOn ` U. K ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    cJ
    cuni
    #
    ctopon
    cfv
    wcel
    #
    wa
    @0
    cK
    cuni
    #
    @1
    wceq
    #
    wa
    cJ
    @3
    ctopon
    cfv
    wcel
    @2
    @4
    @0
    @2
    @1
    @3
    @1
    cK
    toponuni
    eqcomd
    anim2i
    @3
    cJ
    istopon
    sylibr
end
