include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wne.mm"
include "wceq.mm"
include "clat.mm"
include "cbs.mm"
include "simpll.mm"
include "hllat.mm"
include "syl.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2l.mm"
include "eqid.mm"
include "atbase.mm"
include "ltrncl.mm"
include "syl3anc.mm"
include "simpr3l.mm"
include "hlatjcl.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "latmcl.mm"
include "latlej1.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "cdlemc3.mm"
include "syld.mm"
include "necon3bd.mm"
include "3impia.mm"

theorem cdlemc4
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemc3.l: |- .<_ = ( le ` K )
  assume cdlemc3.j: |- .\/ = ( join ` K )
  assume cdlemc3.m: |- ./\ = ( meet ` K )
  assume cdlemc3.a: |- A = ( Atoms ` K )
  assume cdlemc3.h: |- H = ( LHyp ` K )
  assume cdlemc3.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemc3.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ -. Q .<_ ( P .\/ ( F ` P ) ) ) -> ( Q .\/ ( R ` F ) ) =/= ( ( F ` P ) .\/ ( ( P .\/ Q ) ./\ W ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cF
    cT
    wcel
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cQ
    cP
    cP
    cF
    cfv
    #
    c.or
    co
    c.le
    wbr
    #
    wn
    cQ
    cF
    cR
    cfv
    c.or
    co
    #
    @11
    cP
    cQ
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    wne
    @2
    @10
    wa
    #
    @12
    @13
    @16
    @17
    @13
    @16
    wceq
    #
    @11
    @13
    c.le
    wbr
    #
    @12
    @17
    @19
    @18
    @11
    @16
    c.le
    wbr
    #
    @17
    cK
    clat
    wcel
    #
    @11
    cK
    cbs
    cfv
    #
    wcel
    #
    @15
    @22
    wcel
    #
    @20
    @17
    @0
    @21
    @0
    @1
    @10
    simpll
    #
    cK
    hllat
    syl
    #
    @17
    @2
    @3
    cP
    @22
    wcel
    #
    @23
    @2
    @10
    simpl
    @2
    @3
    @6
    @9
    simpr1
    @17
    @4
    @27
    @4
    @5
    @3
    @9
    @2
    simpr2l
    #
    cA
    @22
    cP
    cK
    @22
    eqid
    #
    cdlemc3.a
    atbase
    syl
    @22
    cT
    cF
    cH
    cK
    chlt
    cW
    cP
    @29
    cdlemc3.h
    cdlemc3.t
    ltrncl
    syl3anc
    @17
    @21
    @14
    @22
    wcel
    #
    cW
    @22
    wcel
    #
    @24
    @26
    @17
    @0
    @4
    @7
    @30
    @25
    @28
    @7
    @8
    @3
    @6
    @2
    simpr3l
    cA
    @22
    c.or
    cK
    cP
    cQ
    @29
    cdlemc3.j
    cdlemc3.a
    hlatjcl
    syl3anc
    @1
    @31
    @0
    @10
    @22
    cH
    cK
    cW
    @29
    cdlemc3.h
    lhpbase
    ad2antlr
    @22
    cK
    c.an
    @14
    cW
    @29
    cdlemc3.m
    latmcl
    syl3anc
    @22
    c.or
    cK
    c.le
    @11
    @15
    @29
    cdlemc3.l
    cdlemc3.j
    latlej1
    syl3anc
    @13
    @16
    @11
    c.le
    breq2
    syl5ibrcom
    cA
    cP
    cQ
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemc3.l
    cdlemc3.j
    cdlemc3.m
    cdlemc3.a
    cdlemc3.h
    cdlemc3.t
    cdlemc3.r
    cdlemc3
    syld
    necon3bd
    3impia
end
