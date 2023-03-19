include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "co.mm"
include "cclwwlkn.mm"
include "cc0.mm"
include "wceq.mm"
include "cmin.mm"
include "w3a.mm"
include "cv.mm"
include "crab.mm"
include "numclwwlkovg.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "3anass.mm"
include "syl6bbr.mm"

theorem numclwwlkovgel
  let vw: setvar w
  let vv: setvar v
  let cC: class C
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume numclwwlkovg.c: |- C = ( v e. V , n e. ( ZZ>= ` 2 ) |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) = ( w ` 0 ) ) } )

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint N n
  disjoint N v
  disjoint N w
  disjoint V n
  disjoint V v
  disjoint X n
  disjoint X v
  disjoint X w
  disjoint W w
  assert |- ( ( X e. V /\ N e. ( ZZ>= ` 2 ) ) -> ( W e. ( X C N ) <-> ( W e. ( N ClWWalksN G ) /\ ( W ` 0 ) = X /\ ( W ` ( N - 2 ) ) = ( W ` 0 ) ) ) )

  proof
    cX
    cV
    wcel
    cN
    c2
    cuz
    cfv
    wcel
    wa
    #
    cW
    cX
    cN
    cC
    co
    #
    wcel
    #
    cW
    cN
    cG
    cclwwlkn
    co
    #
    wcel
    #
    cc0
    cW
    cfv
    #
    cX
    wceq
    #
    cN
    c2
    cmin
    co
    #
    cW
    cfv
    #
    @5
    wceq
    #
    wa
    #
    wa
    #
    @4
    @6
    @9
    w3a
    @0
    @2
    cW
    cc0
    vw
    cv
    #
    cfv
    #
    cX
    wceq
    #
    @7
    @12
    cfv
    #
    @13
    wceq
    #
    wa
    #
    vw
    @3
    crab
    #
    wcel
    @11
    @0
    @1
    @18
    cW
    vw
    vv
    cC
    vn
    cG
    cN
    cV
    cX
    numclwwlkovg.c
    numclwwlkovg
    eleq2d
    @17
    @10
    vw
    cW
    @3
    @12
    cW
    wceq
    #
    @14
    @6
    @16
    @9
    @19
    @13
    @5
    cX
    cc0
    @12
    cW
    fveq1
    #
    eqeq1d
    @19
    @15
    @8
    @13
    @5
    @7
    @12
    cW
    fveq1
    @20
    eqeq12d
    anbi12d
    elrab
    syl6bb
    @4
    @6
    @9
    3anass
    syl6bbr
end
