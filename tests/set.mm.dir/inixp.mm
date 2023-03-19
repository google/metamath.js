include "cixp.mm"
include "cin.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "an4.mm"
include "anidm.mm"
include "r19.26.mm"
include "elin.mm"
include "bicomi.mm"
include "ralbii.mm"
include "bitr3i.mm"
include "anbi12i.mm"
include "bitri.mm"
include "vex.mm"
include "elixp.mm"
include "3bitr4i.mm"
include "ineqri.mm"

theorem inixp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f

  disjoint A x
  disjoint f x
  disjoint A f
  disjoint B f
  disjoint C f
  assert |- ( X_ x e. A B i^i X_ x e. A C ) = X_ x e. A ( B i^i C )

  proof
    vf
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
    vx
    cA
    cB
    cC
    cin
    #
    cixp
    #
    vf
    cv
    #
    cA
    wfn
    #
    vx
    cv
    @4
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    @5
    @6
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
    #
    @5
    @6
    @2
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    @4
    @0
    wcel
    #
    @4
    @1
    wcel
    #
    wa
    @4
    @3
    wcel
    @13
    @5
    @5
    wa
    #
    @8
    @11
    wa
    #
    wa
    @16
    @5
    @8
    @5
    @11
    an4
    @19
    @5
    @20
    @15
    @5
    anidm
    @20
    @7
    @10
    wa
    #
    vx
    cA
    wral
    @15
    @7
    @10
    vx
    cA
    r19.26
    @21
    @14
    vx
    cA
    @14
    @21
    @6
    cB
    cC
    elin
    bicomi
    ralbii
    bitr3i
    anbi12i
    bitri
    @17
    @9
    @18
    @12
    vx
    cA
    cB
    @4
    vf
    vex
    #
    elixp
    vx
    cA
    cC
    @4
    @22
    elixp
    anbi12i
    vx
    cA
    @2
    @4
    @22
    elixp
    3bitr4i
    ineqri
end
