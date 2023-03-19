include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cmpt.mm"
include "ssel.mm"
include "anim1d.mm"
include "ssopab2dv.mm"
include "df-mpt.mm"
include "3sstr4g.mm"

theorem mptssALT
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  assert |- ( A C_ B -> ( x e. A |-> C ) C_ ( x e. B |-> C ) )

  proof
    cA
    cB
    wss
    #
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    cC
    wceq
    #
    wa
    #
    vx
    vy
    copab
    @1
    cB
    wcel
    #
    @3
    wa
    #
    vx
    vy
    copab
    vx
    cA
    cC
    cmpt
    vx
    cB
    cC
    cmpt
    @0
    @4
    @6
    vx
    vy
    @0
    @2
    @5
    @3
    cA
    cB
    @1
    ssel
    anim1d
    ssopab2dv
    vx
    vy
    cA
    cC
    df-mpt
    vx
    vy
    cB
    cC
    df-mpt
    3sstr4g
end
