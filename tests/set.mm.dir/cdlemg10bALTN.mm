include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simp11.mm"
include "simp12.mm"
include "jca.mm"
include "3simpc.mm"
include "simp13.mm"
include "eqid.mm"
include "cdlemg2k.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "cp0.mm"
include "simp2.mm"
include "ltrnel.mm"
include "lhpmat.mm"
include "syl2anc.mm"
include "cbs.mm"
include "simp2l.mm"
include "ltrnat.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp3l.mm"
include "hlatjcl.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latmle2.mm"
include "atmod4i2.mm"
include "syl131anc.mm"
include "col.mm"
include "hlol.mm"
include "olj02.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"

theorem cdlemg10bALTN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemg8.l: |- .<_ = ( le ` K )
  assume cdlemg8.j: |- .\/ = ( join ` K )
  assume cdlemg8.m: |- ./\ = ( meet ` K )
  assume cdlemg8.a: |- A = ( Atoms ` K )
  assume cdlemg8.h: |- H = ( LHyp ` K )
  assume cdlemg8.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H /\ F e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( ( ( F ` P ) .\/ ( F ` Q ) ) ./\ W ) = ( ( P .\/ Q ) ./\ W ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    cF
    cT
    wcel
    #
    w3a
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
    cP
    cF
    cfv
    #
    cQ
    cF
    cfv
    c.or
    co
    #
    cW
    c.an
    co
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
    cW
    c.an
    co
    #
    @14
    @10
    @12
    @15
    cW
    c.an
    @10
    @0
    @1
    wa
    #
    @6
    @9
    wa
    @2
    @12
    @15
    wceq
    @10
    @0
    @1
    @0
    @1
    @2
    @6
    @9
    simp11
    #
    @0
    @1
    @2
    @6
    @9
    simp12
    #
    jca
    #
    @3
    @6
    @9
    3simpc
    @0
    @1
    @2
    @6
    @9
    simp13
    #
    cA
    cP
    cQ
    cT
    @14
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg8.h
    cdlemg8.t
    cdlemg8.l
    cdlemg8.j
    cdlemg8.a
    cdlemg8.m
    @14
    eqid
    cdlemg2k
    syl3anc
    oveq1d
    @10
    @11
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
    @10
    @22
    @24
    @14
    c.or
    @10
    @17
    @11
    cA
    wcel
    #
    @11
    cW
    c.le
    wbr
    wn
    wa
    #
    @22
    @24
    wceq
    @20
    @10
    @17
    @2
    @6
    @27
    @20
    @21
    @3
    @6
    @9
    simp2
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrnel
    syl3anc
    cA
    @11
    cH
    cK
    c.le
    c.an
    cW
    @24
    cdlemg8.l
    cdlemg8.m
    @24
    eqid
    #
    cdlemg8.a
    cdlemg8.h
    lhpmat
    syl2anc
    oveq1d
    @10
    @0
    @26
    @14
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @29
    wcel
    #
    @14
    cW
    c.le
    wbr
    #
    @23
    @16
    wceq
    @18
    @10
    @17
    @2
    @4
    @26
    @20
    @21
    @3
    @4
    @5
    @9
    simp2l
    #
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrnat
    syl3anc
    @10
    cK
    clat
    wcel
    #
    @13
    @29
    wcel
    #
    @31
    @30
    @10
    @0
    @34
    @18
    cK
    hllat
    syl
    #
    @10
    @0
    @4
    @7
    @35
    @18
    @33
    @3
    @6
    @7
    @8
    simp3l
    cA
    @29
    c.or
    cK
    cP
    cQ
    @29
    eqid
    #
    cdlemg8.j
    cdlemg8.a
    hlatjcl
    syl3anc
    #
    @10
    @1
    @31
    @19
    @29
    cH
    cK
    cW
    @37
    cdlemg8.h
    lhpbase
    syl
    #
    @29
    cK
    c.an
    @13
    cW
    @37
    cdlemg8.m
    latmcl
    syl3anc
    #
    @39
    @10
    @34
    @35
    @31
    @32
    @36
    @38
    @39
    @29
    cK
    c.le
    c.an
    @13
    cW
    @37
    cdlemg8.l
    cdlemg8.m
    latmle2
    syl3anc
    cA
    @29
    @11
    c.or
    cK
    c.le
    c.an
    @14
    cW
    @37
    cdlemg8.l
    cdlemg8.j
    cdlemg8.m
    cdlemg8.a
    atmod4i2
    syl131anc
    @10
    cK
    col
    wcel
    #
    @30
    @25
    @14
    wceq
    @10
    @0
    @41
    @18
    cK
    hlol
    syl
    @40
    @29
    c.or
    cK
    @14
    @24
    @37
    cdlemg8.j
    @28
    olj02
    syl2anc
    3eqtr3d
    eqtrd
end
