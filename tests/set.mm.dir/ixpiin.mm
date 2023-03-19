include "c0.mm"
include "wne.mm"
include "cixp.mm"
include "ciin.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "r19.28zv.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "elixp.mm"
include "ralbii.mm"
include "bitri.mm"
include "fvex.mm"
include "ralcom.mm"
include "anbi2i.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "eqcomd.mm"

theorem ixpiin
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint B f
  disjoint C f
  assert |- ( B =/= (/) -> X_ x e. A |^|_ y e. B C = |^|_ y e. B X_ x e. A C )

  proof
    cB
    c0
    wne
    #
    vy
    cB
    vx
    cA
    cC
    cixp
    #
    ciin
    #
    vx
    cA
    vy
    cB
    cC
    ciin
    #
    cixp
    #
    @0
    vf
    @2
    @4
    @0
    vf
    cv
    #
    cA
    wfn
    #
    vx
    cv
    #
    @5
    cfv
    #
    cC
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    vy
    cB
    wral
    #
    @6
    @10
    vy
    cB
    wral
    #
    wa
    #
    @5
    @2
    wcel
    #
    @5
    @4
    wcel
    #
    @6
    @10
    vy
    cB
    r19.28zv
    @15
    @5
    @1
    wcel
    #
    vy
    cB
    wral
    #
    @12
    @5
    cvv
    wcel
    @15
    @18
    wb
    vf
    vex
    #
    vy
    @5
    cB
    @1
    cvv
    eliin
    ax-mp
    @17
    @11
    vy
    cB
    vx
    cA
    cC
    @5
    @19
    elixp
    ralbii
    bitri
    @16
    @6
    @8
    @3
    wcel
    #
    vx
    cA
    wral
    #
    wa
    @14
    vx
    cA
    @3
    @5
    @19
    elixp
    @21
    @13
    @6
    @21
    @9
    vy
    cB
    wral
    #
    vx
    cA
    wral
    @13
    @20
    @22
    vx
    cA
    @8
    cvv
    wcel
    @20
    @22
    wb
    @7
    @5
    fvex
    vy
    @8
    cB
    cC
    cvv
    eliin
    ax-mp
    ralbii
    @9
    vx
    vy
    cA
    cB
    ralcom
    bitri
    anbi2i
    bitri
    3bitr4g
    eqrdv
    eqcomd
end
