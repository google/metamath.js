include "cop.mm"
include "co.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "cdm.mm"
include "dmmpt2ssx.mm"
include "elfvdm.mm"
include "df-ov.mm"
include "eleq2s.mm"
include "sseldi.mm"
include "fveq2.mm"
include "opeliunxp2.mm"
include "simprbi.mm"
include "syl.mm"
include "op1stg.mm"
include "eleq2d.mm"
include "syl5ib.mm"

theorem mpt2xopn0yelv
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mpt2xopn0yelv.f: |- F = ( x e. _V , y e. ( 1st ` x ) |-> C )

  disjoint x y
  disjoint K x
  disjoint V x
  disjoint W x
  assert |- ( ( V e. X /\ W e. Y ) -> ( N e. ( <. V , W >. F K ) -> K e. V ) )

  proof
    cN
    cV
    cW
    cop
    #
    cK
    cF
    co
    #
    wcel
    #
    cK
    @0
    c1st
    cfv
    #
    wcel
    #
    cV
    cX
    wcel
    cW
    cY
    wcel
    wa
    #
    cK
    cV
    wcel
    @2
    @0
    cK
    cop
    #
    vx
    cvv
    vx
    cv
    #
    csn
    @7
    c1st
    cfv
    #
    cxp
    ciun
    #
    wcel
    #
    @4
    @2
    cF
    cdm
    #
    @9
    @6
    vx
    vy
    cvv
    @8
    cC
    cF
    mpt2xopn0yelv.f
    dmmpt2ssx
    @6
    @11
    wcel
    cN
    @6
    cF
    cfv
    @1
    cN
    @6
    cF
    elfvdm
    @0
    cK
    cF
    df-ov
    eleq2s
    sseldi
    @10
    @0
    cvv
    wcel
    @4
    vx
    cvv
    @8
    @0
    cK
    @3
    @7
    @0
    c1st
    fveq2
    opeliunxp2
    simprbi
    syl
    @5
    @3
    cV
    cK
    cV
    cW
    cX
    cY
    op1stg
    eleq2d
    syl5ib
end
