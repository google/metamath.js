include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "cotp.mm"
include "elxp2.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "rexxp.mm"
include "df-ot.mm"
include "eqcomi.mm"
include "eqeq2i.mm"
include "rexbii.mm"
include "3bitri.mm"

theorem el2xptp
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vp: setvar p

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint A p
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint B p
  disjoint C p
  disjoint D p
  assert |- ( A e. ( ( B X. C ) X. D ) <-> E. x e. B E. y e. C E. z e. D A = <. x , y , z >. )

  proof
    cA
    cB
    cC
    cxp
    #
    cD
    cxp
    wcel
    cA
    vp
    cv
    #
    vz
    cv
    #
    cop
    #
    wceq
    #
    vz
    cD
    wrex
    #
    vp
    @0
    wrex
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @2
    cop
    #
    wceq
    #
    vz
    cD
    wrex
    #
    vy
    cC
    wrex
    #
    vx
    cB
    wrex
    cA
    @6
    @7
    @2
    cotp
    #
    wceq
    #
    vz
    cD
    wrex
    #
    vy
    cC
    wrex
    #
    vx
    cB
    wrex
    vp
    vz
    cA
    @0
    cD
    elxp2
    @5
    @11
    vp
    vx
    vy
    cB
    cC
    @1
    @8
    wceq
    #
    @4
    @10
    vz
    cD
    @17
    @3
    @9
    cA
    @1
    @8
    @2
    opeq1
    eqeq2d
    rexbidv
    rexxp
    @12
    @16
    vx
    cB
    @11
    @15
    vy
    cC
    @10
    @14
    vz
    cD
    @9
    @13
    cA
    @13
    @9
    @6
    @7
    @2
    df-ot
    eqcomi
    eqeq2i
    rexbii
    rexbii
    rexbii
    3bitri
end
