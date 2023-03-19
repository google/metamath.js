include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "ciin.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cint.mm"
include "cvv.mm"
include "dfiin2g.mm"
include "adantl.mm"
include "wex.mm"
include "wi.mm"
include "elisset.mm"
include "rgenw.mm"
include "r19.2z.mm"
include "mpan2.mm"
include "r19.35.mm"
include "sylib.mm"
include "imp.mm"
include "rexcom4.mm"
include "abn0.mm"
include "sylibr.mm"
include "intex.mm"
include "eqeltrd.mm"

theorem iinexg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( ( A =/= (/) /\ A. x e. A B e. C ) -> |^|_ x e. A B e. _V )

  proof
    cA
    c0
    wne
    #
    cB
    cC
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    vx
    cA
    cB
    ciin
    #
    vy
    cv
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    #
    cint
    #
    cvv
    @2
    @4
    @8
    wceq
    @0
    vx
    vy
    cA
    cB
    cC
    dfiin2g
    adantl
    @3
    @7
    c0
    wne
    #
    @8
    cvv
    wcel
    @3
    @6
    vy
    wex
    #
    @9
    @3
    @5
    vy
    wex
    #
    vx
    cA
    wrex
    #
    @10
    @0
    @2
    @12
    @0
    @1
    @11
    wi
    #
    vx
    cA
    wrex
    #
    @2
    @12
    wi
    @0
    @13
    vx
    cA
    wral
    @14
    @13
    vx
    cA
    vy
    cB
    cC
    elisset
    rgenw
    @13
    vx
    cA
    r19.2z
    mpan2
    @1
    @11
    vx
    cA
    r19.35
    sylib
    imp
    @5
    vx
    vy
    cA
    rexcom4
    sylib
    @6
    vy
    abn0
    sylibr
    @7
    intex
    sylib
    eqeltrd
end
