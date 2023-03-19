include "c0.mm"
include "wne.mm"
include "cint.mm"
include "cixp.mm"
include "cv.mm"
include "ciin.mm"
include "wceq.mm"
include "ixpeq2.mm"
include "wcel.mm"
include "intiin.mm"
include "a1i.mm"
include "mprg.mm"
include "ixpiin.mm"
include "syl5eq.mm"

theorem ixpint
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cC: class C

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint B f
  disjoint C f
  assert |- ( B =/= (/) -> X_ x e. A |^| B = |^|_ y e. B X_ x e. A y )

  proof
    cB
    c0
    wne
    vx
    cA
    cB
    cint
    #
    cixp
    #
    vx
    cA
    vy
    cB
    vy
    cv
    #
    ciin
    #
    cixp
    #
    vy
    cB
    vx
    cA
    @2
    cixp
    ciin
    @0
    @3
    wceq
    #
    @1
    @4
    wceq
    vx
    cA
    vx
    cA
    @0
    @3
    ixpeq2
    @5
    vx
    cv
    cA
    wcel
    vy
    cB
    intiin
    a1i
    mprg
    vx
    vy
    cA
    cB
    @2
    ixpiin
    syl5eq
end
