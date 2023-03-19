include "wf1o.mm"
include "wf1.mm"
include "wfo.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wfn.mm"
include "crn.mm"
include "w3a.mm"
include "df-f1o.mm"
include "dff13.mm"
include "df-fo.mm"
include "anbi12i.mm"
include "df-3an.mm"
include "wss.mm"
include "eqimss.mm"
include "anim2i.mm"
include "df-f.mm"
include "sylibr.mm"
include "pm4.71ri.mm"
include "anbi1i.mm"
include "an32.mm"
include "3bitrri.mm"
include "3bitri.mm"

theorem dff1o6
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  assert |- ( F : A -1-1-onto-> B <-> ( F Fn A /\ ran F = B /\ A. x e. A A. y e. A ( ( F ` x ) = ( F ` y ) -> x = y ) ) )

  proof
    cA
    cB
    cF
    wf1o
    cA
    cB
    cF
    wf1
    #
    cA
    cB
    cF
    wfo
    #
    wa
    cA
    cB
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    vy
    cv
    #
    cF
    cfv
    wceq
    @3
    @4
    wceq
    wi
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    #
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    wceq
    #
    wa
    #
    wa
    #
    @7
    @9
    @5
    w3a
    #
    cA
    cB
    cF
    df-f1o
    @0
    @6
    @1
    @10
    vx
    vy
    cA
    cB
    cF
    dff13
    cA
    cB
    cF
    df-fo
    anbi12i
    @12
    @10
    @5
    wa
    @2
    @10
    wa
    #
    @5
    wa
    @11
    @7
    @9
    @5
    df-3an
    @10
    @13
    @5
    @10
    @2
    @10
    @7
    @8
    cB
    wss
    #
    wa
    @2
    @9
    @14
    @7
    @8
    cB
    eqimss
    anim2i
    cA
    cB
    cF
    df-f
    sylibr
    pm4.71ri
    anbi1i
    @2
    @10
    @5
    an32
    3bitrri
    3bitri
end
