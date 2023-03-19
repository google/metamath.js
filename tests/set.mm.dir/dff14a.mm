include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wne.mm"
include "dff13.mm"
include "wn.mm"
include "con34b.mm"
include "df-ne.mm"
include "bicomi.mm"
include "imbi12i.mm"
include "bitri.mm"
include "2ralbii.mm"
include "anbi2i.mm"

theorem dff14a
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
  assert |- ( F : A -1-1-> B <-> ( F : A --> B /\ A. x e. A A. y e. A ( x =/= y -> ( F ` x ) =/= ( F ` y ) ) ) )

  proof
    cA
    cB
    cF
    wf1
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
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    @0
    @1
    @3
    wne
    #
    @2
    @4
    wne
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    vx
    vy
    cA
    cB
    cF
    dff13
    @8
    @12
    @0
    @7
    @11
    vx
    vy
    cA
    cA
    @7
    @6
    wn
    #
    @5
    wn
    #
    wi
    @11
    @5
    @6
    con34b
    @13
    @9
    @14
    @10
    @9
    @13
    @1
    @3
    df-ne
    bicomi
    @10
    @14
    @2
    @4
    df-ne
    bicomi
    imbi12i
    bitri
    2ralbii
    anbi2i
    bitri
end
