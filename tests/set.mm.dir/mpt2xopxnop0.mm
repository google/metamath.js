include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "wn.mm"
include "cv.mm"
include "wex.mm"
include "neq0.mm"
include "cop.mm"
include "csn.mm"
include "c1st.mm"
include "cfv.mm"
include "ciun.mm"
include "cdm.mm"
include "dmmpt2ssx.mm"
include "elfvdm.mm"
include "df-ov.mm"
include "eleq2s.mm"
include "sseldi.mm"
include "wa.mm"
include "fveq2.mm"
include "opeliunxp2.mm"
include "wi.mm"
include "cuni.mm"
include "eluni.mm"
include "wne.mm"
include "ne0i.mm"
include "ad2antlr.mm"
include "dmsnn0.mm"
include "sylibr.mm"
include "ex.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "1stval.mm"
include "impcom.mm"
include "syl.mm"
include "con1i.mm"

theorem mpt2xopxnop0
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let vn: setvar n
  let cX: class X
  let cY: class Y
  assume mpt2xopn0yelv.f: |- F = ( x e. _V , y e. ( 1st ` x ) |-> C )

  disjoint x y
  disjoint K x
  disjoint V x
  disjoint F x
  disjoint W x
  disjoint K n
  disjoint F n
  disjoint V n
  disjoint W n
  disjoint X n
  disjoint Y n
  assert |- ( -. V e. ( _V X. _V ) -> ( V F K ) = (/) )

  proof
    cV
    cK
    cF
    co
    #
    c0
    wceq
    #
    cV
    cvv
    cvv
    cxp
    wcel
    #
    @1
    wn
    vx
    cv
    #
    @0
    wcel
    #
    vx
    wex
    @2
    vx
    @0
    neq0
    @4
    @2
    vx
    @4
    cV
    cK
    cop
    #
    vx
    cvv
    @3
    csn
    @3
    c1st
    cfv
    #
    cxp
    ciun
    #
    wcel
    #
    @2
    @4
    cF
    cdm
    #
    @7
    @5
    vx
    vy
    cvv
    @6
    cC
    cF
    mpt2xopn0yelv.f
    dmmpt2ssx
    @5
    @9
    wcel
    @3
    @5
    cF
    cfv
    @0
    @3
    @5
    cF
    elfvdm
    cV
    cK
    cF
    df-ov
    eleq2s
    sseldi
    @8
    cV
    cvv
    wcel
    #
    cK
    cV
    c1st
    cfv
    #
    wcel
    #
    wa
    @2
    vx
    cvv
    @6
    cV
    cK
    @11
    @3
    cV
    c1st
    fveq2
    opeliunxp2
    @12
    @10
    @2
    @10
    @2
    wi
    #
    cK
    cV
    csn
    cdm
    #
    cuni
    #
    @11
    cK
    @15
    wcel
    cK
    vn
    cv
    #
    wcel
    #
    @16
    @14
    wcel
    #
    wa
    #
    vn
    wex
    @13
    vn
    cK
    @14
    eluni
    @19
    @13
    vn
    @19
    @10
    @2
    @19
    @10
    wa
    @14
    c0
    wne
    #
    @2
    @18
    @20
    @17
    @10
    @14
    @16
    ne0i
    ad2antlr
    cV
    dmsnn0
    sylibr
    ex
    exlimiv
    sylbi
    cV
    1stval
    eleq2s
    impcom
    sylbi
    syl
    exlimiv
    sylbi
    con1i
end
