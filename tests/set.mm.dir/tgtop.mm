include "ctop.mm"
include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "eltg3.mm"
include "simpr.mm"
include "uniopn.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "expl.mm"
include "exlimdv.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "bastg.mm"
include "eqssd.mm"

theorem tgtop
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cB: class B
  let cV: class V
  let cC: class C


  assert |- ( J e. Top -> ( topGen ` J ) = J )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    ctg
    cfv
    #
    cJ
    @0
    vx
    @1
    cJ
    @0
    vx
    cv
    #
    @1
    wcel
    vy
    cv
    #
    cJ
    wss
    #
    @2
    @3
    cuni
    #
    wceq
    #
    wa
    #
    vy
    wex
    @2
    cJ
    wcel
    #
    vy
    @2
    cJ
    ctop
    eltg3
    @0
    @7
    @8
    vy
    @0
    @4
    @6
    @8
    @0
    @4
    wa
    #
    @6
    wa
    @2
    @5
    cJ
    @9
    @6
    simpr
    @9
    @5
    cJ
    wcel
    @6
    @3
    cJ
    uniopn
    adantr
    eqeltrd
    expl
    exlimdv
    sylbid
    ssrdv
    cJ
    ctop
    bastg
    eqssd
end
