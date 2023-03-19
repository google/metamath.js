include "wlim.mm"
include "word.mm"
include "c0.mm"
include "wcel.mm"
include "cuni.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "csuc.mm"
include "wral.mm"
include "dflim2.mm"
include "wa.mm"
include "ordunisuc2.mm"
include "anbi2d.mm"
include "pm5.32i.mm"
include "3anass.mm"
include "3bitr4i.mm"
include "bitri.mm"

theorem dflim4
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( Lim A <-> ( Ord A /\ (/) e. A /\ A. x e. A suc x e. A ) )

  proof
    cA
    wlim
    cA
    word
    #
    c0
    cA
    wcel
    #
    cA
    cA
    cuni
    wceq
    #
    w3a
    #
    @0
    @1
    vx
    cv
    csuc
    cA
    wcel
    vx
    cA
    wral
    #
    w3a
    #
    cA
    dflim2
    @0
    @1
    @2
    wa
    #
    wa
    @0
    @1
    @4
    wa
    #
    wa
    @3
    @5
    @0
    @6
    @7
    @0
    @2
    @4
    @1
    vx
    cA
    ordunisuc2
    anbi2d
    pm5.32i
    @0
    @1
    @2
    3anass
    @0
    @1
    @4
    3anass
    3bitr4i
    bitri
end
