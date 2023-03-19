include "cixp.mm"
include "cv.mm"
include "wcel.mm"
include "cab.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "df-ixp.mm"
include "abid2.mm"
include "fneq2i.mm"
include "anbi1i.mm"
include "abbii.mm"
include "eqtri.mm"

theorem dfixp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f

  disjoint f x
  disjoint A f
  disjoint B f
  disjoint A x
  assert |- X_ x e. A B = { f | ( f Fn A /\ A. x e. A ( f ` x ) e. B ) }

  proof
    vx
    cA
    cB
    cixp
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
    #
    wfn
    #
    @1
    @0
    cfv
    cB
    wcel
    vx
    cA
    wral
    #
    wa
    #
    vf
    cab
    @0
    cA
    wfn
    #
    @4
    wa
    #
    vf
    cab
    vx
    cA
    cB
    vf
    df-ixp
    @5
    @7
    vf
    @3
    @6
    @4
    @2
    cA
    @0
    vx
    cA
    abid2
    fneq2i
    anbi1i
    abbii
    eqtri
end
