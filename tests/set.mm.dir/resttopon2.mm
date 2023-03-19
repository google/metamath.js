include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ctop.mm"
include "cin.mm"
include "cuni.mm"
include "wceq.mm"
include "topontop.mm"
include "resttop.mm"
include "sylan.mm"
include "toponuni.mm"
include "ineq2d.mm"
include "adantr.mm"
include "eqid.mm"
include "restuni2.mm"
include "eqtrd.mm"
include "istopon.mm"
include "sylanbrc.mm"

theorem resttopon2
  let cA: class A
  let cJ: class J
  let cV: class V
  let cX: class X


  assert |- ( ( J e. ( TopOn ` X ) /\ A e. V ) -> ( J |`t A ) e. ( TopOn ` ( A i^i X ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    cJ
    cA
    crest
    co
    #
    ctop
    wcel
    #
    cA
    cX
    cin
    #
    @3
    cuni
    #
    wceq
    @3
    @5
    ctopon
    cfv
    wcel
    @0
    cJ
    ctop
    wcel
    #
    @1
    @4
    cX
    cJ
    topontop
    #
    cA
    cJ
    cV
    resttop
    sylan
    @2
    @5
    cA
    cJ
    cuni
    #
    cin
    #
    @6
    @0
    @5
    @10
    wceq
    @1
    @0
    cX
    @9
    cA
    cX
    cJ
    toponuni
    ineq2d
    adantr
    @0
    @7
    @1
    @10
    @6
    wceq
    @8
    cA
    cJ
    cV
    @9
    @9
    eqid
    restuni2
    sylan
    eqtrd
    @5
    @3
    istopon
    sylanbrc
end
