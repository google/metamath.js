include "ciin.mm"
include "cin.mm"
include "cxp.mm"
include "wceq.mm"
include "c0.mm"
include "cvv.mm"
include "iineq1.mm"
include "0iin.mm"
include "syl6eq.mm"
include "ineq2d.mm"
include "inv1.mm"
include "xpeq2d.mm"
include "eqtr4d.mm"
include "wne.mm"
include "xpindi.mm"
include "xpiindi.mm"
include "syl5eq.mm"
include "pm2.61ine.mm"

theorem xpriindi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
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
  assert |- ( C X. ( D i^i |^|_ x e. A B ) ) = ( ( C X. D ) i^i |^|_ x e. A ( C X. B ) )

  proof
    cC
    cD
    vx
    cA
    cB
    ciin
    #
    cin
    #
    cxp
    #
    cC
    cD
    cxp
    #
    vx
    cA
    cC
    cB
    cxp
    #
    ciin
    #
    cin
    #
    wceq
    cA
    c0
    cA
    c0
    wceq
    #
    @2
    @3
    @6
    @7
    @1
    cD
    cC
    @7
    @1
    cD
    cvv
    cin
    cD
    @7
    @0
    cvv
    cD
    @7
    @0
    vx
    c0
    cB
    ciin
    cvv
    vx
    cA
    c0
    cB
    iineq1
    vx
    cB
    0iin
    syl6eq
    ineq2d
    cD
    inv1
    syl6eq
    xpeq2d
    @7
    @6
    @3
    cvv
    cin
    @3
    @7
    @5
    cvv
    @3
    @7
    @5
    vx
    c0
    @4
    ciin
    cvv
    vx
    cA
    c0
    @4
    iineq1
    vx
    @4
    0iin
    syl6eq
    ineq2d
    @3
    inv1
    syl6eq
    eqtr4d
    cA
    c0
    wne
    #
    @2
    @3
    cC
    @0
    cxp
    #
    cin
    @6
    cC
    cD
    @0
    xpindi
    @8
    @9
    @5
    @3
    vx
    cA
    cB
    cC
    xpiindi
    ineq2d
    syl5eq
    pm2.61ine
end
