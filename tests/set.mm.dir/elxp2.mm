include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cxp.mm"
include "wrex.mm"
include "ancom.mm"
include "2exbii.mm"
include "elxp.mm"
include "r2ex.mm"
include "3bitr4i.mm"

theorem elxp2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  assert |- ( A e. ( B X. C ) <-> E. x e. B E. y e. C A = <. x , y >. )

  proof
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    wceq
    #
    @0
    cB
    wcel
    @1
    cC
    wcel
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    @3
    @2
    wa
    #
    vy
    wex
    vx
    wex
    cA
    cB
    cC
    cxp
    wcel
    @2
    vy
    cC
    wrex
    vx
    cB
    wrex
    @4
    @5
    vx
    vy
    @2
    @3
    ancom
    2exbii
    vx
    vy
    cA
    cB
    cC
    elxp
    @2
    vx
    vy
    cB
    cC
    r2ex
    3bitr4i
end
