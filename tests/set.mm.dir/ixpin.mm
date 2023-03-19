include "cin.mm"
include "cixp.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "anandi.mm"
include "elin.mm"
include "ralbii.mm"
include "r19.26.mm"
include "bitri.mm"
include "anbi2i.mm"
include "vex.mm"
include "elixp.mm"
include "anbi12i.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem ixpin
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let cF: class F

  disjoint A x
  disjoint f x
  disjoint A f
  disjoint B f
  disjoint F x
  disjoint C f
  assert |- X_ x e. A ( B i^i C ) = ( X_ x e. A B i^i X_ x e. A C )

  proof
    vf
    vx
    cA
    cB
    cC
    cin
    #
    cixp
    #
    vx
    cA
    cB
    cixp
    #
    vx
    cA
    cC
    cixp
    #
    cin
    #
    vf
    cv
    #
    cA
    wfn
    #
    vx
    cv
    @5
    cfv
    #
    @0
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    @5
    @2
    wcel
    #
    @5
    @3
    wcel
    #
    wa
    #
    @5
    @1
    wcel
    @5
    @4
    wcel
    @6
    @7
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @7
    cC
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    wa
    @6
    @15
    wa
    #
    @6
    @17
    wa
    #
    wa
    @10
    @13
    @6
    @15
    @17
    anandi
    @9
    @18
    @6
    @9
    @14
    @16
    wa
    #
    vx
    cA
    wral
    @18
    @8
    @21
    vx
    cA
    @7
    cB
    cC
    elin
    ralbii
    @14
    @16
    vx
    cA
    r19.26
    bitri
    anbi2i
    @11
    @19
    @12
    @20
    vx
    cA
    cB
    @5
    vf
    vex
    #
    elixp
    vx
    cA
    cC
    @5
    @22
    elixp
    anbi12i
    3bitr4i
    vx
    cA
    @0
    @5
    @22
    elixp
    @5
    @2
    @3
    elin
    3bitr4i
    eqriv
end
