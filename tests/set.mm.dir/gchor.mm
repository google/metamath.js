include "cgch.mm"
include "wcel.mm"
include "cfn.mm"
include "wn.mm"
include "wa.mm"
include "cdom.mm"
include "wbr.mm"
include "cpw.mm"
include "csdm.mm"
include "cen.mm"
include "wo.mm"
include "simprr.mm"
include "brdom2.mm"
include "sylib.mm"
include "wi.mm"
include "gchen1.mm"
include "expr.mm"
include "adantrr.mm"
include "orim1d.mm"
include "mpd.mm"

theorem gchor
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A e. GCH /\ -. A e. Fin ) /\ ( A ~<_ B /\ B ~<_ ~P A ) ) -> ( A ~~ B \/ B ~~ ~P A ) )

  proof
    cA
    cgch
    wcel
    cA
    cfn
    wcel
    wn
    wa
    #
    cA
    cB
    cdom
    wbr
    #
    cB
    cA
    cpw
    #
    cdom
    wbr
    #
    wa
    wa
    #
    cB
    @2
    csdm
    wbr
    #
    cB
    @2
    cen
    wbr
    #
    wo
    #
    cA
    cB
    cen
    wbr
    #
    @6
    wo
    @4
    @3
    @7
    @0
    @1
    @3
    simprr
    cB
    @2
    brdom2
    sylib
    @4
    @5
    @8
    @6
    @0
    @1
    @5
    @8
    wi
    @3
    @0
    @1
    @5
    @8
    cA
    cB
    gchen1
    expr
    adantrr
    orim1d
    mpd
end
