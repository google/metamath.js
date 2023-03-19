include "wcel.mm"
include "cv.mm"
include "csuc.mm"
include "wf.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "com.mm"
include "wrex.mm"
include "cab.mm"
include "eleq2i.mm"
include "feq1.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "rexbidv.mm"
include "elab.mm"
include "weq.mm"
include "suceq.mm"
include "feq2d.mm"
include "raleq.mm"
include "3anbi13d.mm"
include "cbvrexv.mm"
include "3bitri.mm"

theorem axdc3lem3
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vs: setvar s
  assume axdc3lem3.1: |- A e. _V
  assume axdc3lem3.2: |- S = { s | E. n e. _om ( s : suc n --> A /\ ( s ` (/) ) = C /\ A. k e. n ( s ` suc k ) e. ( F ` ( s ` k ) ) ) }
  assume axdc3lem3.3: |- B e. _V

  disjoint A m
  disjoint A n
  disjoint A s
  disjoint n s
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint B s
  disjoint k s
  disjoint C m
  disjoint C n
  disjoint C s
  disjoint F m
  disjoint F n
  disjoint F s
  assert |- ( B e. S <-> E. m e. _om ( B : suc m --> A /\ ( B ` (/) ) = C /\ A. k e. m ( B ` suc k ) e. ( F ` ( B ` k ) ) ) )

  proof
    cB
    cS
    wcel
    cB
    vn
    cv
    #
    csuc
    #
    cA
    vs
    cv
    #
    wf
    #
    c0
    @2
    cfv
    #
    cC
    wceq
    #
    vk
    cv
    #
    csuc
    #
    @2
    cfv
    #
    @6
    @2
    cfv
    #
    cF
    cfv
    #
    wcel
    #
    vk
    @0
    wral
    #
    w3a
    #
    vn
    com
    wrex
    #
    vs
    cab
    #
    wcel
    @1
    cA
    cB
    wf
    #
    c0
    cB
    cfv
    #
    cC
    wceq
    #
    @7
    cB
    cfv
    #
    @6
    cB
    cfv
    #
    cF
    cfv
    #
    wcel
    #
    vk
    @0
    wral
    #
    w3a
    #
    vn
    com
    wrex
    #
    vm
    cv
    #
    csuc
    #
    cA
    cB
    wf
    #
    @18
    @22
    vk
    @26
    wral
    #
    w3a
    #
    vm
    com
    wrex
    cS
    @15
    cB
    axdc3lem3.2
    eleq2i
    @14
    @25
    vs
    cB
    axdc3lem3.3
    @2
    cB
    wceq
    #
    @13
    @24
    vn
    com
    @31
    @3
    @16
    @5
    @18
    @12
    @23
    @1
    cA
    @2
    cB
    feq1
    @31
    @4
    @17
    cC
    c0
    @2
    cB
    fveq1
    eqeq1d
    @31
    @11
    @22
    vk
    @0
    @31
    @8
    @19
    @10
    @21
    @7
    @2
    cB
    fveq1
    @31
    @9
    @20
    cF
    @6
    @2
    cB
    fveq1
    fveq2d
    eleq12d
    ralbidv
    3anbi123d
    rexbidv
    elab
    @24
    @30
    vn
    vm
    com
    vn
    vm
    weq
    #
    @16
    @28
    @23
    @29
    @18
    @32
    @1
    @27
    cA
    cB
    @0
    @26
    suceq
    feq2d
    @22
    vk
    @0
    @26
    raleq
    3anbi13d
    cbvrexv
    3bitri
end
