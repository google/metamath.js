include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "ctg.mm"
include "cfv.mm"
include "w3a.mm"
include "tgss.mm"
include "3adant3.mm"
include "wceq.mm"
include "tgtop.mm"
include "3ad2ant1.mm"
include "sseqtrd.mm"
include "simp3.mm"
include "eqssd.mm"

theorem basgen
  let cB: class B
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cV: class V


  assert |- ( ( J e. Top /\ B C_ J /\ J C_ ( topGen ` B ) ) -> ( topGen ` B ) = J )

  proof
    cJ
    ctop
    wcel
    #
    cB
    cJ
    wss
    #
    cJ
    cB
    ctg
    cfv
    #
    wss
    #
    w3a
    #
    @2
    cJ
    @4
    @2
    cJ
    ctg
    cfv
    #
    cJ
    @0
    @1
    @2
    @5
    wss
    @3
    cB
    cJ
    ctop
    tgss
    3adant3
    @0
    @1
    @5
    cJ
    wceq
    @3
    cJ
    tgtop
    3ad2ant1
    sseqtrd
    @0
    @1
    @3
    simp3
    eqssd
end
