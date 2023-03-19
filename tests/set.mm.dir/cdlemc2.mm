include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "simp1l.mm"
include "simp3ll.mm"
include "simp3rl.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp3l.mm"
include "cdlemc1.mm"
include "breqtrrd.mm"
include "wb.mm"
include "simp2.mm"
include "clat.mm"
include "hllat.mm"
include "latjcl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "ltrnle.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "ltrnj.mm"
include "latmle2.mm"
include "ltrnval1.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "breqtrd.mm"

theorem cdlemc2
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
  assume cdlemc2.l: |- .<_ = ( le ` K )
  assume cdlemc2.j: |- .\/ = ( join ` K )
  assume cdlemc2.m: |- ./\ = ( meet ` K )
  assume cdlemc2.a: |- A = ( Atoms ` K )
  assume cdlemc2.h: |- H = ( LHyp ` K )
  assume cdlemc2.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) ) -> ( F ` Q ) .<_ ( ( F ` P ) .\/ ( ( P .\/ Q ) ./\ W ) ) )

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
    wa
    #
    w3a
    #
    cQ
    cF
    cfv
    #
    cP
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
    cF
    cfv
    #
    cP
    cF
    cfv
    #
    @14
    c.or
    co
    #
    c.le
    @11
    cQ
    @15
    c.le
    wbr
    #
    @12
    @16
    c.le
    wbr
    #
    @11
    cQ
    @13
    @15
    c.le
    @11
    @0
    @4
    @7
    cQ
    @13
    c.le
    wbr
    @0
    @1
    @3
    @10
    simp1l
    #
    @4
    @5
    @9
    @2
    @3
    simp3ll
    #
    @7
    @8
    @6
    @2
    @3
    simp3rl
    #
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdlemc2.l
    cdlemc2.j
    cdlemc2.a
    hlatlej2
    syl3anc
    @11
    @2
    cQ
    cK
    cbs
    cfv
    #
    wcel
    #
    @6
    @15
    @13
    wceq
    @2
    @3
    @10
    simp1
    #
    @11
    @7
    @25
    @23
    cA
    @24
    cQ
    cK
    @24
    eqid
    #
    cdlemc2.a
    atbase
    syl
    #
    @2
    @3
    @6
    @9
    simp3l
    cA
    @24
    cP
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cQ
    @27
    cdlemc2.l
    cdlemc2.j
    cdlemc2.m
    cdlemc2.a
    cdlemc2.h
    cdlemc1
    syl3anc
    breqtrrd
    @11
    @2
    @3
    @25
    @15
    @24
    wcel
    #
    @19
    @20
    wb
    @26
    @2
    @3
    @10
    simp2
    #
    @28
    @11
    cK
    clat
    wcel
    #
    cP
    @24
    wcel
    #
    @14
    @24
    wcel
    #
    @29
    @11
    @0
    @31
    @21
    cK
    hllat
    syl
    #
    @11
    @4
    @32
    @22
    cA
    @24
    cP
    cK
    @27
    cdlemc2.a
    atbase
    syl
    #
    @11
    @31
    @13
    @24
    wcel
    #
    cW
    @24
    wcel
    #
    @33
    @34
    @11
    @31
    @32
    @25
    @36
    @34
    @35
    @28
    @24
    c.or
    cK
    cP
    cQ
    @27
    cdlemc2.j
    latjcl
    syl3anc
    #
    @11
    @1
    @37
    @0
    @1
    @3
    @10
    simp1r
    @24
    cH
    cK
    cW
    @27
    cdlemc2.h
    lhpbase
    syl
    #
    @24
    cK
    c.an
    @13
    cW
    @27
    cdlemc2.m
    latmcl
    syl3anc
    #
    @24
    c.or
    cK
    cP
    @14
    @27
    cdlemc2.j
    latjcl
    syl3anc
    @24
    cT
    cF
    cH
    cK
    c.le
    chlt
    cW
    cQ
    @15
    @27
    cdlemc2.l
    cdlemc2.h
    cdlemc2.t
    ltrnle
    syl112anc
    mpbid
    @11
    @16
    @17
    @14
    cF
    cfv
    #
    c.or
    co
    #
    @18
    @11
    @2
    @3
    @32
    @33
    @16
    @42
    wceq
    @26
    @30
    @35
    @40
    @24
    cT
    cF
    cH
    c.or
    cK
    cW
    cP
    @14
    @27
    cdlemc2.j
    cdlemc2.h
    cdlemc2.t
    ltrnj
    syl112anc
    @11
    @41
    @14
    @17
    c.or
    @11
    @2
    @3
    @33
    @14
    cW
    c.le
    wbr
    #
    @41
    @14
    wceq
    @26
    @30
    @40
    @11
    @31
    @36
    @37
    @43
    @34
    @38
    @39
    @24
    cK
    c.le
    c.an
    @13
    cW
    @27
    cdlemc2.l
    cdlemc2.m
    latmle2
    syl3anc
    @24
    cT
    cF
    cH
    cK
    c.le
    chlt
    cW
    @14
    @27
    cdlemc2.l
    cdlemc2.h
    cdlemc2.t
    ltrnval1
    syl112anc
    oveq2d
    eqtrd
    breqtrd
end
