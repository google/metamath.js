include "wel.mm"
include "wa.mm"
include "wrex.mm"
include "wsb.mm"
include "nfv.mm"
include "weq.mm"
include "elequ1.mm"
include "bi2anan9r.mm"
include "rexbidv.mm"
include "sbiedv.mm"
include "sbie.mm"

theorem prtlem5
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let vs: setvar s
  let vr: setvar r

  disjoint u v
  disjoint u x
  disjoint r u
  disjoint v x
  disjoint r v
  disjoint r x
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint A u
  disjoint A v
  disjoint A x
  assert |- ( [ s / v ] [ r / u ] E. x e. A ( u e. x /\ v e. x ) <-> E. x e. A ( r e. x /\ s e. x ) )

  proof
    vu
    vx
    wel
    #
    vv
    vx
    wel
    #
    wa
    #
    vx
    cA
    wrex
    #
    vu
    vr
    wsb
    vr
    vx
    wel
    #
    vs
    vx
    wel
    #
    wa
    #
    vx
    cA
    wrex
    #
    vv
    vs
    @7
    vv
    nfv
    vv
    vs
    weq
    #
    @3
    @7
    vu
    vr
    @8
    vu
    vr
    weq
    #
    wa
    @2
    @6
    vx
    cA
    @9
    @0
    @4
    @8
    @1
    @5
    vu
    vr
    vx
    elequ1
    vv
    vs
    vx
    elequ1
    bi2anan9r
    rexbidv
    sbiedv
    sbie
end
