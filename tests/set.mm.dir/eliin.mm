include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "ciin.mm"
include "wceq.mm"
include "eleq1.mm"
include "ralbidv.mm"
include "df-iin.mm"
include "elab2g.mm"

theorem eliin
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( A e. V -> ( A e. |^|_ x e. B C <-> A. x e. B A e. C ) )

  proof
    vy
    cv
    #
    cC
    wcel
    #
    vx
    cB
    wral
    cA
    cC
    wcel
    #
    vx
    cB
    wral
    vy
    cA
    vx
    cB
    cC
    ciin
    cV
    @0
    cA
    wceq
    @1
    @2
    vx
    cB
    @0
    cA
    cC
    eleq1
    ralbidv
    vx
    vy
    cB
    cC
    df-iin
    elab2g
end
