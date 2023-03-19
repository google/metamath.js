include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "copab.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "df-xp.mm"
include "eleq2i.mm"
include "elopab.mm"
include "bitri.mm"

theorem elxp
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
  assert |- ( A e. ( B X. C ) <-> E. x E. y ( A = <. x , y >. /\ ( x e. B /\ y e. C ) ) )

  proof
    cA
    cB
    cC
    cxp
    #
    wcel
    cA
    vx
    cv
    #
    cB
    wcel
    vy
    cv
    #
    cC
    wcel
    wa
    #
    vx
    vy
    copab
    #
    wcel
    cA
    @1
    @2
    cop
    wceq
    @3
    wa
    vy
    wex
    vx
    wex
    @0
    @4
    cA
    vx
    vy
    cB
    cC
    df-xp
    eleq2i
    @3
    vx
    vy
    cA
    elopab
    bitri
end
