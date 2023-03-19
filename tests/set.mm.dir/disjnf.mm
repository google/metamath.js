include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wo.mm"
include "wdisj.mm"
include "wcel.mm"
include "wmo.mm"
include "inidm.mm"
include "eqeq1i.mm"
include "orbi1i.mm"
include "eqidd.mm"
include "disjor.mm"
include "orcom.mm"
include "ralbii.mm"
include "r19.32v.mm"
include "bitri.mm"
include "3bitri.mm"
include "moel.mm"
include "orbi2i.mm"
include "3bitr4i.mm"

theorem disjnf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( Disj_ x e. A B <-> ( B = (/) \/ E* x x e. A ) )

  proof
    cB
    cB
    cin
    #
    c0
    wceq
    #
    vx
    cv
    #
    vy
    cv
    wceq
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wo
    #
    cB
    c0
    wceq
    #
    @5
    wo
    vx
    cA
    cB
    wdisj
    #
    @7
    @2
    cA
    wcel
    vx
    wmo
    #
    wo
    @1
    @7
    @5
    @0
    cB
    c0
    cB
    inidm
    eqeq1i
    orbi1i
    @8
    @3
    @1
    wo
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    @1
    @4
    wo
    #
    vx
    cA
    wral
    @6
    cA
    cB
    cB
    vx
    vy
    @3
    cB
    eqidd
    disjor
    @11
    @12
    vx
    cA
    @11
    @1
    @3
    wo
    #
    vy
    cA
    wral
    @12
    @10
    @13
    vy
    cA
    @3
    @1
    orcom
    ralbii
    @1
    @3
    vy
    cA
    r19.32v
    bitri
    ralbii
    @1
    @4
    vx
    cA
    r19.32v
    3bitri
    @9
    @5
    @7
    vx
    vy
    cA
    moel
    orbi2i
    3bitr4i
end
