include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cuni.mm"
include "ctg.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "simpr.mm"
include "pwuni.mm"
include "jctir.mm"
include "ssin.mm"
include "sylib.mm"
include "unissd.mm"
include "wb.mm"
include "eltg.mm"
include "adantr.mm"
include "mpbird.mm"

theorem eltg3i
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cC: class C


  assert |- ( ( B e. V /\ A C_ B ) -> U. A e. ( topGen ` B ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    wss
    #
    wa
    #
    cA
    cuni
    #
    cB
    ctg
    cfv
    wcel
    #
    @3
    cB
    @3
    cpw
    #
    cin
    #
    cuni
    wss
    #
    @2
    cA
    @6
    @2
    @1
    cA
    @5
    wss
    #
    wa
    cA
    @6
    wss
    @2
    @1
    @8
    @0
    @1
    simpr
    cA
    pwuni
    jctir
    cA
    cB
    @5
    ssin
    sylib
    unissd
    @0
    @4
    @7
    wb
    @1
    @3
    cB
    cV
    eltg
    adantr
    mpbird
end
