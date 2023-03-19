include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "simp1l.mm"
include "simp22l.mm"
include "simp23l.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "clat.mm"
include "cbs.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "latabs2.mm"
include "eqtrd.mm"
include "cp0.mm"
include "simp1.mm"
include "simp22.mm"
include "simp21.mm"
include "simp3.mm"
include "trl0.mm"
include "syl112anc.mm"
include "col.mm"
include "hlol.mm"
include "olj01.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "hlatjcl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latjcom.mm"
include "cp1.mm"
include "hlatlej1.mm"
include "atmod2i1.mm"
include "syl131anc.mm"
include "lhpjat1.mm"
include "syl21anc.mm"
include "olm11.mm"
include "3eqtrd.mm"
include "oveq12d.mm"
include "ltrnateq.mm"
include "3eqtr4rd.mm"

theorem cdlemc6
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F ` P ) = P ) -> ( F ` Q ) = ( ( Q .\/ ( R ` F ) ) ./\ ( ( F ` P ) .\/ ( ( P .\/ Q ) ./\ W ) ) ) )

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
    cP
    cF
    cfv
    #
    cP
    wceq
    #
    w3a
    #
    cQ
    cP
    cQ
    c.or
    co
    #
    c.an
    co
    #
    cQ
    cQ
    cF
    cR
    cfv
    #
    c.or
    co
    #
    @11
    @14
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    cQ
    cF
    cfv
    @13
    @15
    cQ
    cQ
    cP
    c.or
    co
    #
    c.an
    co
    #
    cQ
    @13
    @14
    @20
    cQ
    c.an
    @13
    @0
    @4
    @7
    @14
    @20
    wceq
    @0
    @1
    @10
    @12
    simp1l
    #
    @4
    @5
    @3
    @9
    @2
    @12
    simp22l
    #
    @7
    @8
    @3
    @6
    @2
    @12
    simp23l
    #
    cA
    c.or
    cK
    cP
    cQ
    cdlemc3.j
    cdlemc3.a
    hlatjcom
    syl3anc
    oveq2d
    @13
    cK
    clat
    wcel
    #
    cQ
    cK
    cbs
    cfv
    #
    wcel
    #
    cP
    @26
    wcel
    #
    @21
    cQ
    wceq
    @13
    @0
    @25
    @22
    cK
    hllat
    syl
    #
    @13
    @7
    @27
    @24
    cA
    @26
    cQ
    cK
    @26
    eqid
    #
    cdlemc3.a
    atbase
    syl
    #
    @13
    @4
    @28
    @23
    cA
    @26
    cP
    cK
    @30
    cdlemc3.a
    atbase
    syl
    #
    @26
    c.or
    cK
    c.an
    cQ
    cP
    @30
    cdlemc3.j
    cdlemc3.m
    latabs2
    syl3anc
    eqtrd
    @13
    @17
    cQ
    @19
    @14
    c.an
    @13
    @17
    cQ
    cK
    cp0
    cfv
    #
    c.or
    co
    #
    cQ
    @13
    @16
    @33
    cQ
    c.or
    @13
    @2
    @6
    @3
    @12
    @16
    @33
    wceq
    @2
    @10
    @12
    simp1
    @2
    @3
    @6
    @9
    @12
    simp22
    #
    @2
    @3
    @6
    @9
    @12
    simp21
    @2
    @10
    @12
    simp3
    #
    cA
    cP
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    @33
    cdlemc3.l
    @33
    eqid
    #
    cdlemc3.a
    cdlemc3.h
    cdlemc3.t
    cdlemc3.r
    trl0
    syl112anc
    oveq2d
    @13
    cK
    col
    wcel
    #
    @27
    @34
    cQ
    wceq
    @13
    @0
    @38
    @22
    cK
    hlol
    syl
    #
    @31
    @26
    c.or
    cK
    cQ
    @33
    @30
    cdlemc3.j
    @37
    olj01
    syl2anc
    eqtrd
    @13
    @19
    cP
    @18
    c.or
    co
    #
    @18
    cP
    c.or
    co
    #
    @14
    @13
    @11
    cP
    @18
    c.or
    @36
    oveq1d
    @13
    @25
    @28
    @18
    @26
    wcel
    #
    @40
    @41
    wceq
    @29
    @32
    @13
    @25
    @14
    @26
    wcel
    #
    cW
    @26
    wcel
    #
    @42
    @29
    @13
    @0
    @4
    @7
    @43
    @22
    @23
    @24
    cA
    @26
    c.or
    cK
    cP
    cQ
    @30
    cdlemc3.j
    cdlemc3.a
    hlatjcl
    syl3anc
    #
    @13
    @1
    @44
    @0
    @1
    @10
    @12
    simp1r
    #
    @26
    cH
    cK
    cW
    @30
    cdlemc3.h
    lhpbase
    syl
    #
    @26
    cK
    c.an
    @14
    cW
    @30
    cdlemc3.m
    latmcl
    syl3anc
    @26
    c.or
    cK
    cP
    @18
    @30
    cdlemc3.j
    latjcom
    syl3anc
    @13
    @41
    @14
    cW
    cP
    c.or
    co
    #
    c.an
    co
    #
    @14
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    @14
    @13
    @0
    @4
    @43
    @44
    cP
    @14
    c.le
    wbr
    #
    @41
    @49
    wceq
    @22
    @23
    @45
    @47
    @13
    @0
    @4
    @7
    @52
    @22
    @23
    @24
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdlemc3.l
    cdlemc3.j
    cdlemc3.a
    hlatlej1
    syl3anc
    cA
    @26
    cP
    c.or
    cK
    c.le
    c.an
    @14
    cW
    @30
    cdlemc3.l
    cdlemc3.j
    cdlemc3.m
    cdlemc3.a
    atmod2i1
    syl131anc
    @13
    @48
    @50
    @14
    c.an
    @13
    @0
    @1
    @6
    @48
    @50
    wceq
    @22
    @46
    @35
    cA
    cP
    @50
    cH
    c.or
    cK
    c.le
    cW
    cdlemc3.l
    cdlemc3.j
    @50
    eqid
    #
    cdlemc3.a
    cdlemc3.h
    lhpjat1
    syl21anc
    oveq2d
    @13
    @38
    @43
    @51
    @14
    wceq
    @39
    @45
    @26
    @50
    cK
    c.an
    @14
    @30
    cdlemc3.m
    @53
    olm11
    syl2anc
    3eqtrd
    3eqtrd
    oveq12d
    cA
    cP
    cQ
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemc3.l
    cdlemc3.a
    cdlemc3.h
    cdlemc3.t
    ltrnateq
    3eqtr4rd
end
