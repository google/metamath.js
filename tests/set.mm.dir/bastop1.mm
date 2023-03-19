include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "cuni.mm"
include "wex.mm"
include "wb.mm"
include "tgss.mm"
include "tgtop.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "eqss.mm"
include "baib.mm"
include "syl.mm"
include "dfss3.mm"
include "syl6bb.mm"
include "cvv.mm"
include "ssexg.mm"
include "ancoms.mm"
include "eltg3.mm"
include "ralbidv.mm"
include "bitrd.mm"

theorem bastop1
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cJ: class J

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint J x
  disjoint J y
  assert |- ( ( J e. Top /\ B C_ J ) -> ( ( topGen ` B ) = J <-> A. x e. J E. y ( y C_ B /\ x = U. y ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cB
    cJ
    wss
    #
    wa
    #
    cB
    ctg
    cfv
    #
    cJ
    wceq
    #
    vx
    cv
    #
    @3
    wcel
    #
    vx
    cJ
    wral
    #
    vy
    cv
    #
    cB
    wss
    @5
    @8
    cuni
    wceq
    wa
    vy
    wex
    #
    vx
    cJ
    wral
    @2
    @4
    cJ
    @3
    wss
    #
    @7
    @2
    @3
    cJ
    wss
    #
    @4
    @10
    wb
    @2
    @3
    cJ
    ctg
    cfv
    #
    cJ
    cB
    cJ
    ctop
    tgss
    @0
    @12
    cJ
    wceq
    @1
    cJ
    tgtop
    adantr
    sseqtrd
    @4
    @11
    @10
    @3
    cJ
    eqss
    baib
    syl
    vx
    cJ
    @3
    dfss3
    syl6bb
    @2
    @6
    @9
    vx
    cJ
    @2
    cB
    cvv
    wcel
    #
    @6
    @9
    wb
    @1
    @0
    @13
    cB
    cJ
    ctop
    ssexg
    ancoms
    vy
    @5
    cB
    cvv
    eltg3
    syl
    ralbidv
    bitrd
end
