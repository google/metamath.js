include "csn.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "ffnfv.mm"
include "fvex.mm"
include "elsn.mm"
include "ralbii.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem fconstfv
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint A x
  disjoint B x
  disjoint F x
  assert |- ( F : A --> { B } <-> ( F Fn A /\ A. x e. A ( F ` x ) = B ) )

  proof
    cA
    cB
    csn
    #
    cF
    wf
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
    @0
    wcel
    #
    vx
    cA
    wral
    #
    wa
    @1
    @3
    cB
    wceq
    #
    vx
    cA
    wral
    #
    wa
    vx
    cA
    @0
    cF
    ffnfv
    @5
    @7
    @1
    @4
    @6
    vx
    cA
    @3
    cB
    @2
    cF
    fvex
    elsn
    ralbii
    anbi2i
    bitri
end
