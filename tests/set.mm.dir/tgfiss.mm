include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfi.mm"
include "cfv.mm"
include "ctg.mm"
include "fiss.mm"
include "wceq.mm"
include "fitop.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "tgss.mm"
include "syldan.mm"
include "tgtop.mm"

theorem tgfiss
  let cA: class A
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( ( J e. Top /\ A C_ J ) -> ( topGen ` ( fi ` A ) ) C_ J )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cJ
    wss
    #
    wa
    #
    cA
    cfi
    cfv
    #
    ctg
    cfv
    #
    cJ
    ctg
    cfv
    #
    cJ
    @0
    @1
    @3
    cJ
    wss
    @4
    @5
    wss
    @2
    @3
    cJ
    cfi
    cfv
    #
    cJ
    cA
    cJ
    ctop
    fiss
    @0
    @6
    cJ
    wceq
    @1
    cJ
    fitop
    adantr
    sseqtrd
    @3
    cJ
    ctop
    tgss
    syldan
    @0
    @5
    cJ
    wceq
    @1
    cJ
    tgtop
    adantr
    sseqtrd
end
