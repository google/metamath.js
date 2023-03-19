include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "wne.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "dff14a.mm"
include "necom.mm"
include "imbi1i.mm"
include "ralbii.mm"
include "raldifsnb.mm"
include "bitri.mm"
include "anbi2i.mm"

theorem dff14b
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
  assert |- ( F : A -1-1-> B <-> ( F : A --> B /\ A. x e. A A. y e. ( A \ { x } ) ( F ` x ) =/= ( F ` y ) ) )

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
    vy
    cv
    #
    wne
    #
    @1
    cF
    cfv
    @2
    cF
    cfv
    wne
    #
    wi
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wa
    @0
    @4
    vy
    cA
    @1
    csn
    cdif
    wral
    #
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
    dff14a
    @7
    @9
    @0
    @6
    @8
    vx
    cA
    @6
    @2
    @1
    wne
    #
    @4
    wi
    #
    vy
    cA
    wral
    @8
    @5
    @11
    vy
    cA
    @3
    @10
    @4
    @1
    @2
    necom
    imbi1i
    ralbii
    @4
    vy
    cA
    @1
    raldifsnb
    bitri
    ralbii
    anbi2i
    bitri
end
