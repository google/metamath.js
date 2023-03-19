include "wss.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "cab.mm"
include "wfn.mm"
include "cfv.mm"
include "wa.mm"
include "cixp.mm"
include "ssel.mm"
include "ral2imi.mm"
include "anim2d.mm"
include "ss2abdv.mm"
include "df-ixp.mm"
include "3sstr4g.mm"

theorem ss2ixp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f


  assert |- ( A. x e. A B C_ C -> X_ x e. A B C_ X_ x e. A C )

  proof
    cB
    cC
    wss
    #
    vx
    cA
    wral
    #
    vf
    cv
    #
    vx
    cv
    #
    cA
    wcel
    vx
    cab
    wfn
    #
    @3
    @2
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
    @4
    @5
    cC
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
    vx
    cA
    cB
    cixp
    vx
    cA
    cC
    cixp
    @1
    @8
    @11
    vf
    @1
    @7
    @10
    @4
    @0
    @6
    @9
    vx
    cA
    cB
    cC
    @5
    ssel
    ral2imi
    anim2d
    ss2abdv
    vx
    cA
    cB
    vf
    df-ixp
    vx
    cA
    cC
    vf
    df-ixp
    3sstr4g
end
