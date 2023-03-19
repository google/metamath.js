include "wf1o.mm"
include "id.mm"
include "ccnv.mm"
include "wfun.mm"
include "cv.mm"
include "cima.mm"
include "cvv.mm"
include "wcel.mm"
include "wfo.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "vex.mm"
include "funimaex.mm"
include "syl.mm"
include "f1ofun.mm"
include "f1opw2.mm"

theorem f1opw
  let cA: class A
  let cB: class B
  let cF: class F
  let vb: setvar b
  let va: setvar a

  disjoint A b
  disjoint B b
  disjoint F b
  disjoint a b
  disjoint A a
  disjoint B a
  disjoint F a
  assert |- ( F : A -1-1-onto-> B -> ( b e. ~P A |-> ( F " b ) ) : ~P A -1-1-onto-> ~P B )

  proof
    cA
    cB
    cF
    wf1o
    #
    cA
    cB
    cF
    va
    vb
    @0
    id
    @0
    cF
    ccnv
    #
    wfun
    #
    @1
    va
    cv
    #
    cima
    cvv
    wcel
    @0
    cA
    cB
    cF
    wfo
    @2
    cA
    cB
    cF
    dff1o3
    simprbi
    @1
    @3
    va
    vex
    funimaex
    syl
    @0
    cF
    wfun
    cF
    vb
    cv
    #
    cima
    cvv
    wcel
    cA
    cB
    cF
    f1ofun
    cF
    @4
    vb
    vex
    funimaex
    syl
    f1opw2
end
