include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "wral.mm"
include "cab.mm"
include "ciin.mm"
include "cin.mm"
include "wceq.mm"
include "eleq2d.mm"
include "ralprg.mm"
include "abbidv.mm"
include "df-iin.mm"
include "df-in.mm"
include "3eqtr4g.mm"

theorem iinxprg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cV: class V
  let cW: class W
  let vy: setvar y
  assume iinxprg.1: |- ( x = A -> C = D )
  assume iinxprg.2: |- ( x = B -> C = E )

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint E x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint D y
  disjoint E y
  disjoint V y
  disjoint W y
  assert |- ( ( A e. V /\ B e. W ) -> |^|_ x e. { A , B } C = ( D i^i E ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    vy
    cv
    #
    cC
    wcel
    #
    vx
    cA
    cB
    cpr
    #
    wral
    #
    vy
    cab
    @1
    cD
    wcel
    #
    @1
    cE
    wcel
    #
    wa
    #
    vy
    cab
    vx
    @3
    cC
    ciin
    cD
    cE
    cin
    @0
    @4
    @7
    vy
    @2
    @5
    @6
    vx
    cA
    cB
    cV
    cW
    vx
    cv
    #
    cA
    wceq
    cC
    cD
    @1
    iinxprg.1
    eleq2d
    @8
    cB
    wceq
    cC
    cE
    @1
    iinxprg.2
    eleq2d
    ralprg
    abbidv
    vx
    vy
    @3
    cC
    df-iin
    vy
    cD
    cE
    df-in
    3eqtr4g
end
