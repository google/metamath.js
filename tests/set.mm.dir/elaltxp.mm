include "caltxp.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "caltop.mm"
include "wceq.mm"
include "wrex.mm"
include "elex.mm"
include "wi.mm"
include "wa.mm"
include "altopex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "df-altxp.mm"
include "elab2g.mm"
include "pm5.21nii.mm"

theorem elaltxp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cX: class X
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint X x
  disjoint X y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint X z
  assert |- ( X e. ( A XX. B ) <-> E. x e. A E. y e. B X = << x , y >> )

  proof
    cX
    cA
    cB
    caltxp
    #
    wcel
    cX
    cvv
    wcel
    #
    cX
    vx
    cv
    #
    vy
    cv
    #
    caltop
    #
    wceq
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    cX
    @0
    elex
    @5
    @1
    vx
    vy
    cA
    cB
    @5
    @1
    wi
    @2
    cA
    wcel
    @3
    cB
    wcel
    wa
    @5
    @1
    @4
    cvv
    wcel
    @2
    @3
    altopex
    cX
    @4
    cvv
    eleq1
    mpbiri
    a1i
    rexlimivv
    vz
    cv
    #
    @4
    wceq
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    @6
    vz
    cX
    @0
    cvv
    @7
    cX
    wceq
    @8
    @5
    vx
    vy
    cA
    cB
    @7
    cX
    @4
    eqeq1
    2rexbidv
    vx
    vy
    vz
    cA
    cB
    df-altxp
    elab2g
    pm5.21nii
end
