include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "cixp.mm"
include "nfel2.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "cbvral.mm"
include "anbi2i.mm"
include "abbii.mm"
include "dfixp.mm"
include "3eqtr4i.mm"

theorem cbvixp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  assume cbvixp.1: |- F/_ y B
  assume cbvixp.2: |- F/_ x C
  assume cbvixp.3: |- ( x = y -> B = C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A f
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint C f
  assert |- X_ x e. A B = X_ y e. A C

  proof
    vf
    cv
    #
    cA
    wfn
    #
    vx
    cv
    #
    @0
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    vf
    cab
    @1
    vy
    cv
    #
    @0
    cfv
    #
    cC
    wcel
    #
    vy
    cA
    wral
    #
    wa
    #
    vf
    cab
    vx
    cA
    cB
    cixp
    vy
    cA
    cC
    cixp
    @6
    @11
    vf
    @5
    @10
    @1
    @4
    @9
    vx
    vy
    cA
    vy
    @3
    cB
    cbvixp.1
    nfel2
    vx
    @8
    cC
    cbvixp.2
    nfel2
    vx
    vy
    weq
    @3
    @8
    cB
    cC
    @2
    @7
    @0
    fveq2
    cbvixp.3
    eleq12d
    cbvral
    anbi2i
    abbii
    vx
    cA
    cB
    vf
    dfixp
    vy
    cA
    cC
    vf
    dfixp
    3eqtr4i
end
