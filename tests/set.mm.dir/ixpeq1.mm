include "wceq.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "cixp.mm"
include "fneq2.mm"
include "raleq.mm"
include "anbi12d.mm"
include "abbidv.mm"
include "dfixp.mm"
include "3eqtr4g.mm"

theorem ixpeq1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f

  disjoint A x
  disjoint B x
  disjoint f x
  disjoint A f
  disjoint B f
  disjoint C f
  assert |- ( A = B -> X_ x e. A C = X_ x e. B C )

  proof
    cA
    cB
    wceq
    #
    vf
    cv
    #
    cA
    wfn
    #
    vx
    cv
    @1
    cfv
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
    @1
    cB
    wfn
    #
    @3
    vx
    cB
    wral
    #
    wa
    #
    vf
    cab
    vx
    cA
    cC
    cixp
    vx
    cB
    cC
    cixp
    @0
    @5
    @8
    vf
    @0
    @2
    @6
    @4
    @7
    cA
    cB
    @1
    fneq2
    @3
    vx
    cA
    cB
    raleq
    anbi12d
    abbidv
    vx
    cA
    cC
    vf
    dfixp
    vx
    cB
    cC
    vf
    dfixp
    3eqtr4g
end
