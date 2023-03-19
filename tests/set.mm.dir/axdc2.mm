include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "copab.mm"
include "com.mm"
include "cmpt.mm"
include "weq.mm"
include "wb.mm"
include "eleq1.mm"
include "adantr.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "sylan9bb.mm"
include "anbi12d.mm"
include "cbvopabv.mm"
include "cbvmptv.mm"
include "axdc2lem.mm"

theorem axdc2
  let cA: class A
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let vh: setvar h
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  assume axdc2.1: |- A e. _V

  disjoint A g
  disjoint A k
  disjoint g k
  disjoint F g
  disjoint F k
  disjoint A h
  disjoint g h
  disjoint h k
  disjoint A s
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint h s
  disjoint h t
  disjoint h x
  disjoint h y
  disjoint k s
  disjoint k t
  disjoint k x
  disjoint k y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint F h
  disjoint F s
  disjoint F t
  disjoint F x
  disjoint F y
  disjoint g n
  disjoint h n
  disjoint k n
  disjoint n x
  disjoint n y
  assert |- ( ( A =/= (/) /\ F : A --> ( ~P A \ { (/) } ) ) -> E. g ( g : _om --> A /\ A. k e. _om ( g ` suc k ) e. ( F ` ( g ` k ) ) ) )

  proof
    vx
    vy
    cA
    vs
    cv
    #
    cA
    wcel
    #
    vt
    cv
    #
    @0
    cF
    cfv
    #
    wcel
    #
    wa
    #
    vs
    vt
    copab
    vg
    vh
    vk
    cF
    vn
    com
    vn
    cv
    #
    vh
    cv
    #
    cfv
    #
    cmpt
    axdc2.1
    @5
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    @9
    cF
    cfv
    #
    wcel
    #
    wa
    vs
    vt
    vx
    vy
    vs
    vx
    weq
    #
    vt
    vy
    weq
    #
    wa
    @1
    @10
    @4
    @13
    @14
    @1
    @10
    wb
    @15
    @0
    @9
    cA
    eleq1
    adantr
    @14
    @4
    @2
    @12
    wcel
    @15
    @13
    @14
    @3
    @12
    @2
    @0
    @9
    cF
    fveq2
    eleq2d
    @2
    @11
    @12
    eleq1
    sylan9bb
    anbi12d
    cbvopabv
    vn
    vx
    com
    @8
    @9
    @7
    cfv
    @6
    @9
    @7
    fveq2
    cbvmptv
    axdc2lem
end
