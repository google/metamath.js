include "ciin.mm"
include "cxp.mm"
include "wrel.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "relxp.mm"
include "rgenw.mm"
include "r19.2z.mm"
include "mpan2.mm"
include "reliin.mm"
include "syl.mm"
include "jctil.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "r19.28zv.mm"
include "bicomd.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "anbi2i.mm"
include "opelxp.mm"
include "ralbii.mm"
include "3bitr4g.mm"
include "opex.mm"
include "eqrelrdv2.mm"
include "mpancom.mm"

theorem xpiindi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint C x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C y
  disjoint C z
  disjoint B y
  disjoint B z
  assert |- ( A =/= (/) -> ( C X. |^|_ x e. A B ) = |^|_ x e. A ( C X. B ) )

  proof
    cC
    vx
    cA
    cB
    ciin
    #
    cxp
    #
    wrel
    #
    vx
    cA
    cC
    cB
    cxp
    #
    ciin
    #
    wrel
    #
    wa
    cA
    c0
    wne
    #
    @1
    @4
    wceq
    @6
    @5
    @2
    @6
    @3
    wrel
    #
    vx
    cA
    wrex
    #
    @5
    @6
    @7
    vx
    cA
    wral
    @8
    @7
    vx
    cA
    cC
    cB
    relxp
    rgenw
    @7
    vx
    cA
    r19.2z
    mpan2
    vx
    cA
    @3
    reliin
    syl
    cC
    @0
    relxp
    jctil
    @6
    vy
    vz
    @1
    @4
    @6
    vy
    cv
    #
    cC
    wcel
    #
    vz
    cv
    #
    @0
    wcel
    #
    wa
    #
    @9
    @11
    cop
    #
    @3
    wcel
    #
    vx
    cA
    wral
    #
    @14
    @1
    wcel
    @14
    @4
    wcel
    #
    @6
    @10
    @11
    cB
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    @10
    @18
    wa
    #
    vx
    cA
    wral
    #
    @13
    @16
    @6
    @22
    @20
    @10
    @18
    vx
    cA
    r19.28zv
    bicomd
    @12
    @19
    @10
    @11
    cvv
    wcel
    @12
    @19
    wb
    vz
    vex
    vx
    @11
    cA
    cB
    cvv
    eliin
    ax-mp
    anbi2i
    @15
    @21
    vx
    cA
    @9
    @11
    cC
    cB
    opelxp
    ralbii
    3bitr4g
    @9
    @11
    cC
    @0
    opelxp
    @14
    cvv
    wcel
    @17
    @16
    wb
    @9
    @11
    opex
    vx
    @14
    cA
    @3
    cvv
    eliin
    ax-mp
    3bitr4g
    eqrelrdv2
    mpancom
end
