include "wdisj.mm"
include "wn.mm"
include "cv.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "wral.mm"
include "wrex.mm"
include "wne.mm"
include "wa.mm"
include "disjor.mm"
include "notbii.mm"
include "rexnal.mm"
include "ioran.mm"
include "df-ne.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "rexbii.mm"
include "bitr3i.mm"
include "3bitr2i.mm"

theorem ndisj2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume ndisj2.1: |- ( x = y -> B = C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C x
  assert |- ( -. Disj_ x e. A B <-> E. x e. A E. y e. A ( x =/= y /\ ( B i^i C ) =/= (/) ) )

  proof
    vx
    cA
    cB
    wdisj
    #
    wn
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    cB
    cC
    cin
    #
    c0
    wceq
    #
    wo
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wn
    @7
    wn
    #
    vx
    cA
    wrex
    @1
    @2
    wne
    #
    @4
    c0
    wne
    #
    wa
    #
    vy
    cA
    wrex
    #
    vx
    cA
    wrex
    @0
    @8
    cA
    cB
    cC
    vx
    vy
    ndisj2.1
    disjor
    notbii
    @7
    vx
    cA
    rexnal
    @9
    @13
    vx
    cA
    @9
    @6
    wn
    #
    vy
    cA
    wrex
    @13
    @6
    vy
    cA
    rexnal
    @14
    @12
    vy
    cA
    @14
    @3
    wn
    #
    @5
    wn
    #
    wa
    @12
    @3
    @5
    ioran
    @10
    @15
    @11
    @16
    @1
    @2
    df-ne
    @4
    c0
    df-ne
    anbi12i
    bitr4i
    rexbii
    bitr3i
    rexbii
    3bitr2i
end
