include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "cdlemk8.mm"
include "oveq1d.mm"
include "cp0.mm"
include "wceq.mm"
include "simp1.mm"
include "ltrnel.mm"
include "3adant2r.mm"
include "eqid.mm"
include "lhpmat.mm"
include "syl2anc.mm"
include "simp1l.mm"
include "simp2l.mm"
include "simp3l.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "simp2r.mm"
include "ltrncnv.mm"
include "ltrnco.mm"
include "trlcl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "syl.mm"
include "trlle.mm"
include "atmod4i2.mm"
include "syl131anc.mm"
include "col.mm"
include "hlol.mm"
include "olj02.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"

theorem cdlemk9
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  assume cdlemk.b: |- B = ( Base ` K )
  assume cdlemk.l: |- .<_ = ( le ` K )
  assume cdlemk.j: |- .\/ = ( join ` K )
  assume cdlemk.a: |- A = ( Atoms ` K )
  assume cdlemk.h: |- H = ( LHyp ` K )
  assume cdlemk.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk.m: |- ./\ = ( meet ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( G e. T /\ X e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( ( G ` P ) .\/ ( X ` P ) ) ./\ W ) = ( R ` ( X o. `' G ) ) )

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
    cG
    cT
    wcel
    #
    cX
    cT
    wcel
    #
    wa
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
    w3a
    #
    cP
    cG
    cfv
    #
    cP
    cX
    cfv
    c.or
    co
    #
    cW
    c.an
    co
    @10
    cX
    cG
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    @14
    @9
    @11
    @15
    cW
    c.an
    cA
    cB
    cP
    cR
    cT
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    cdlemk.m
    cdlemk8
    oveq1d
    @9
    @10
    cW
    c.an
    co
    #
    @14
    c.or
    co
    #
    cK
    cp0
    cfv
    #
    @14
    c.or
    co
    #
    @16
    @14
    @9
    @17
    @19
    @14
    c.or
    @9
    @2
    @10
    cA
    wcel
    #
    @10
    cW
    c.le
    wbr
    wn
    wa
    #
    @17
    @19
    wceq
    @2
    @5
    @8
    simp1
    #
    @2
    @3
    @8
    @22
    @4
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrnel
    3adant2r
    cA
    @10
    cH
    cK
    c.le
    c.an
    cW
    @19
    cdlemk.l
    cdlemk.m
    @19
    eqid
    #
    cdlemk.a
    cdlemk.h
    lhpmat
    syl2anc
    oveq1d
    @9
    @0
    @21
    @14
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @14
    cW
    c.le
    wbr
    #
    @18
    @16
    wceq
    @0
    @1
    @5
    @8
    simp1l
    #
    @9
    @2
    @3
    @6
    @21
    @23
    @2
    @3
    @4
    @8
    simp2l
    #
    @2
    @5
    @6
    @7
    simp3l
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrnat
    syl3anc
    @9
    @2
    @13
    cT
    wcel
    #
    @25
    @23
    @9
    @2
    @4
    @12
    cT
    wcel
    #
    @30
    @23
    @2
    @3
    @4
    @8
    simp2r
    @9
    @2
    @3
    @31
    @23
    @29
    cT
    cG
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrncnv
    syl2anc
    cT
    cX
    @12
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrnco
    syl3anc
    #
    cB
    cR
    cT
    @13
    cH
    cK
    cW
    cdlemk.b
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcl
    syl2anc
    #
    @9
    @1
    @26
    @0
    @1
    @5
    @8
    simp1r
    cB
    cH
    cK
    cW
    cdlemk.b
    cdlemk.h
    lhpbase
    syl
    @9
    @2
    @30
    @27
    @23
    @32
    cR
    cT
    @13
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlle
    syl2anc
    cA
    cB
    @10
    c.or
    cK
    c.le
    c.an
    @14
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.m
    cdlemk.a
    atmod4i2
    syl131anc
    @9
    cK
    col
    wcel
    #
    @25
    @20
    @14
    wceq
    @9
    @0
    @34
    @28
    cK
    hlol
    syl
    @33
    cB
    c.or
    cK
    @14
    @19
    cdlemk.b
    cdlemk.j
    @24
    olj02
    syl2anc
    3eqtr3d
    eqtrd
end
