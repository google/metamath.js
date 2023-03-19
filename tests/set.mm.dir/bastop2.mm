include "ctop.mm"
include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cuni.mm"
include "wex.mm"
include "wral.mm"
include "ctb.mm"
include "eleq1.mm"
include "biimparc.mm"
include "tgclb.mm"
include "sylibr.mm"
include "bastg.mm"
include "syl.mm"
include "simpr.mm"
include "sseqtrd.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "bastop1.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem bastop2
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cJ: class J

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint J x
  disjoint J y
  assert |- ( J e. Top -> ( ( topGen ` B ) = J <-> ( B C_ J /\ A. x e. J E. y ( y C_ B /\ x = U. y ) ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cB
    ctg
    cfv
    #
    cJ
    wceq
    #
    cB
    cJ
    wss
    #
    @2
    wa
    @3
    vy
    cv
    #
    cB
    wss
    vx
    cv
    @4
    cuni
    wceq
    wa
    vy
    wex
    vx
    cJ
    wral
    #
    wa
    @0
    @2
    @3
    @0
    @2
    @3
    @0
    @2
    wa
    #
    cB
    @1
    cJ
    @6
    cB
    ctb
    wcel
    #
    cB
    @1
    wss
    @6
    @1
    ctop
    wcel
    #
    @7
    @2
    @8
    @0
    @1
    cJ
    ctop
    eleq1
    biimparc
    cB
    tgclb
    sylibr
    cB
    ctb
    bastg
    syl
    @0
    @2
    simpr
    sseqtrd
    ex
    pm4.71rd
    @0
    @3
    @2
    @5
    vx
    vy
    cB
    cJ
    bastop1
    pm5.32da
    bitrd
end
