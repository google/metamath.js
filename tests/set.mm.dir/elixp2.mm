include "cvv.mm"
include "wcel.mm"
include "cixp.mm"
include "wa.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "w3a.mm"
include "wceq.mm"
include "fneq1.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "dfixp.mm"
include "elab2g.mm"
include "pm5.32i.mm"
include "elex.mm"
include "pm4.71ri.mm"
include "3anass.mm"
include "3bitr4i.mm"

theorem elixp2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vf: setvar f
  let cC: class C
  let cD: class D

  disjoint A x
  disjoint F x
  disjoint f x
  disjoint A f
  disjoint B f
  disjoint C x
  disjoint D x
  disjoint F f
  assert |- ( F e. X_ x e. A B <-> ( F e. _V /\ F Fn A /\ A. x e. A ( F ` x ) e. B ) )

  proof
    cF
    cvv
    wcel
    #
    cF
    vx
    cA
    cB
    cixp
    #
    wcel
    #
    wa
    @0
    cF
    cA
    wfn
    #
    vx
    cv
    #
    cF
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
    wa
    @2
    @0
    @3
    @7
    w3a
    @0
    @2
    @8
    vf
    cv
    #
    cA
    wfn
    #
    @4
    @9
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
    @8
    vf
    cF
    @1
    cvv
    @9
    cF
    wceq
    #
    @10
    @3
    @13
    @7
    cA
    @9
    cF
    fneq1
    @14
    @12
    @6
    vx
    cA
    @14
    @11
    @5
    cB
    @4
    @9
    cF
    fveq1
    eleq1d
    ralbidv
    anbi12d
    vx
    cA
    cB
    vf
    dfixp
    elab2g
    pm5.32i
    @2
    @0
    cF
    @1
    elex
    pm4.71ri
    @0
    @3
    @7
    3anass
    3bitr4i
end
