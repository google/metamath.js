include "cusgr.mm"
include "wcel.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "cc0.mm"
include "c2.mm"
include "cmin.mm"
include "cop.mm"
include "csubstr.mm"
include "c1.mm"
include "cnbgr.mm"
include "wceq.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "wa.mm"
include "extwwlkfab.mm"
include "eleq2d.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "3anbi123d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem extwwlkfabel
  let vw: setvar w
  let vv: setvar v
  let cC: class C
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume extwwlkfab.v: |- V = ( Vtx ` G )
  assume extwwlkfab.c: |- C = ( v e. V , n e. ( ZZ>= ` 2 ) |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) = ( w ` 0 ) ) } )
  assume extwwlkfab.f: |- F = ( X ( ClWWalksNOn ` G ) ( N - 2 ) )

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint X n
  disjoint X v
  disjoint X w
  disjoint N n
  disjoint N v
  disjoint N w
  disjoint F w
  disjoint W w
  assert |- ( ( G e. USGraph /\ X e. V /\ N e. ( ZZ>= ` 3 ) ) -> ( W e. ( X C N ) <-> ( W e. ( N ClWWalksN G ) /\ ( ( W substr <. 0 , ( N - 2 ) >. ) e. F /\ ( W ` ( N - 1 ) ) e. ( G NeighbVtx X ) /\ ( W ` ( N - 2 ) ) = X ) ) ) )

  proof
    cG
    cusgr
    wcel
    cX
    cV
    wcel
    cN
    c3
    cuz
    cfv
    wcel
    w3a
    #
    cW
    cX
    cN
    cC
    co
    #
    wcel
    cW
    vw
    cv
    #
    cc0
    cN
    c2
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    cF
    wcel
    #
    cN
    c1
    cmin
    co
    #
    @2
    cfv
    #
    cG
    cX
    cnbgr
    co
    #
    wcel
    #
    @3
    @2
    cfv
    #
    cX
    wceq
    #
    w3a
    #
    vw
    cN
    cG
    cclwwlkn
    co
    #
    crab
    #
    wcel
    cW
    @14
    wcel
    cW
    @4
    csubstr
    co
    #
    cF
    wcel
    #
    @7
    cW
    cfv
    #
    @9
    wcel
    #
    @3
    cW
    cfv
    #
    cX
    wceq
    #
    w3a
    #
    wa
    @0
    @1
    @15
    cW
    vw
    vv
    cC
    vn
    cF
    cG
    cN
    cV
    cX
    extwwlkfab.v
    extwwlkfab.c
    extwwlkfab.f
    extwwlkfab
    eleq2d
    @13
    @22
    vw
    cW
    @14
    @2
    cW
    wceq
    #
    @6
    @17
    @10
    @19
    @12
    @21
    @23
    @5
    @16
    cF
    @2
    cW
    @4
    csubstr
    oveq1
    eleq1d
    @23
    @8
    @18
    @9
    @7
    @2
    cW
    fveq1
    eleq1d
    @23
    @11
    @20
    cX
    @3
    @2
    cW
    fveq1
    eqeq1d
    3anbi123d
    elrab
    syl6bb
end
