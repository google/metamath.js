include "cv.mm"
include "csuc.mm"
include "wcel.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wceq.mm"
include "wi.mm"
include "com.mm"
include "wral.mm"
include "suceq.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "bnj1113.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "bitri.mm"

theorem bnj222
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vi: setvar i
  let vm: setvar m
  let cF: class F
  let cN: class N
  assume bnj222.1: |- ( ps <-> A. i e. _om ( suc i e. N -> ( F ` suc i ) = U_ y e. ( F ` i ) _pred ( y , A , R ) ) )

  disjoint A i
  disjoint A m
  disjoint i m
  disjoint F i
  disjoint F m
  disjoint F y
  disjoint i y
  disjoint m y
  disjoint N i
  disjoint N m
  disjoint R i
  disjoint R m
  assert |- ( ps <-> A. m e. _om ( suc m e. N -> ( F ` suc m ) = U_ y e. ( F ` m ) _pred ( y , A , R ) ) )

  proof
    wps
    vi
    cv
    #
    csuc
    #
    cN
    wcel
    #
    @1
    cF
    cfv
    #
    vy
    @0
    cF
    cfv
    #
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    #
    wceq
    #
    wi
    #
    vi
    com
    wral
    vm
    cv
    #
    csuc
    #
    cN
    wcel
    #
    @10
    cF
    cfv
    #
    vy
    @9
    cF
    cfv
    #
    @5
    ciun
    #
    wceq
    #
    wi
    #
    vm
    com
    wral
    bnj222.1
    @8
    @16
    vi
    vm
    com
    @0
    @9
    wceq
    #
    @2
    @11
    @7
    @15
    @17
    @1
    @10
    cN
    @0
    @9
    suceq
    #
    eleq1d
    @17
    @3
    @12
    @6
    @14
    @17
    @1
    @10
    cF
    @18
    fveq2d
    vy
    @0
    @9
    @4
    @13
    @5
    @0
    @9
    cF
    fveq2
    bnj1113
    eqeq12d
    imbi12d
    cbvralv
    bitri
end
