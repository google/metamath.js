include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "simp11l.mm"
include "simp22l.mm"
include "simp11.mm"
include "simp21.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "hlatlej2.mm"
include "simp23.mm"
include "oveq2d.mm"
include "simp22.mm"
include "trljat1.mm"
include "eqtr2d.mm"
include "breqtrd.mm"
include "cdlemk14.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "simp12.mm"
include "simp31.mm"
include "trlnidat.mm"
include "hlatjcl.mm"
include "fveq1i.mm"
include "cdlemksat.mm"
include "syl5eqel.mm"
include "simp13.mm"
include "simp33.mm"
include "necomd.mm"
include "trlcocnvat.mm"
include "syl121anc.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"

theorem cdlemk15
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  assume cdlemk1.b: |- B = ( Base ` K )
  assume cdlemk1.l: |- .<_ = ( le ` K )
  assume cdlemk1.j: |- .\/ = ( join ` K )
  assume cdlemk1.m: |- ./\ = ( meet ` K )
  assume cdlemk1.a: |- A = ( Atoms ` K )
  assume cdlemk1.h: |- H = ( LHyp ` K )
  assume cdlemk1.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk1.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk1.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk1.o: |- O = ( S ` D )

  disjoint f i
  disjoint ./\ f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ f
  disjoint .\/ i
  disjoint A i
  disjoint D f
  disjoint D i
  disjoint F f
  disjoint F i
  disjoint H i
  disjoint K i
  disjoint N f
  disjoint N i
  disjoint P f
  disjoint P i
  disjoint R f
  disjoint R i
  disjoint T f
  disjoint T i
  disjoint W f
  disjoint W i
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ ( R ` D ) =/= ( R ` F ) ) ) -> ( N ` P ) .<_ ( ( P .\/ ( R ` F ) ) ./\ ( ( O ` P ) .\/ ( R ` ( F o. `' D ) ) ) ) )

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
    cD
    cT
    wcel
    #
    w3a
    #
    cN
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
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    #
    wceq
    #
    w3a
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    cD
    @14
    wne
    #
    cD
    cR
    cfv
    #
    @10
    wne
    #
    w3a
    #
    w3a
    #
    cP
    cN
    cfv
    #
    cP
    @10
    c.or
    co
    #
    c.le
    wbr
    #
    @21
    cP
    cO
    cfv
    #
    cF
    cD
    ccnv
    ccom
    cR
    cfv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    @21
    @22
    @26
    c.an
    co
    c.le
    wbr
    #
    @20
    @21
    cP
    @21
    c.or
    co
    #
    @22
    c.le
    @20
    @0
    @7
    @21
    cA
    wcel
    #
    @21
    @29
    c.le
    wbr
    @0
    @1
    @3
    @4
    @13
    @19
    simp11l
    #
    @7
    @8
    @6
    @12
    @5
    @19
    simp22l
    #
    @20
    @2
    @6
    @7
    @30
    @2
    @3
    @4
    @13
    @19
    simp11
    #
    @5
    @6
    @9
    @12
    @19
    simp21
    #
    @32
    cA
    cP
    cT
    cN
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    ltrnat
    syl3anc
    #
    cA
    cP
    @21
    c.or
    cK
    c.le
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    hlatlej2
    syl3anc
    @20
    @22
    cP
    @11
    c.or
    co
    #
    @29
    @20
    @10
    @11
    cP
    c.or
    @5
    @6
    @9
    @12
    @19
    simp23
    oveq2d
    @20
    @2
    @6
    @9
    @36
    @29
    wceq
    @33
    @34
    @5
    @6
    @9
    @12
    @19
    simp22
    cA
    cP
    cR
    cT
    cN
    cH
    c.or
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trljat1
    syl3anc
    eqtr2d
    breqtrd
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.m
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.s
    cdlemk1.o
    cdlemk14
    @20
    cK
    clat
    wcel
    #
    @21
    cB
    wcel
    #
    @22
    cB
    wcel
    #
    @26
    cB
    wcel
    #
    @23
    @27
    wa
    @28
    wb
    @20
    @0
    @37
    @31
    cK
    hllat
    syl
    @20
    @30
    @38
    @35
    cA
    cB
    @21
    cK
    cdlemk1.b
    cdlemk1.a
    atbase
    syl
    @20
    @0
    @7
    @10
    cA
    wcel
    #
    @39
    @31
    @32
    @20
    @2
    @3
    @15
    @41
    @33
    @2
    @3
    @4
    @13
    @19
    simp12
    #
    @5
    @13
    @15
    @16
    @18
    simp31
    cA
    cB
    cR
    cT
    cF
    cH
    cK
    cW
    cdlemk1.b
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlnidat
    syl3anc
    cA
    cB
    c.or
    cK
    cP
    @10
    cdlemk1.b
    cdlemk1.j
    cdlemk1.a
    hlatjcl
    syl3anc
    @20
    @0
    @24
    cA
    wcel
    @25
    cA
    wcel
    #
    @40
    @31
    @20
    @24
    cP
    cD
    cS
    cfv
    #
    cfv
    cA
    cP
    cO
    @44
    cdlemk1.o
    fveq1i
    cA
    cB
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cD
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.m
    cdlemk1.s
    cdlemksat
    syl5eqel
    @20
    @2
    @3
    @4
    @10
    @17
    wne
    @43
    @33
    @42
    @2
    @3
    @4
    @13
    @19
    simp13
    @20
    @17
    @10
    @5
    @13
    @15
    @16
    @18
    simp33
    necomd
    cA
    cR
    cT
    cF
    cD
    cH
    cK
    cW
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlcocnvat
    syl121anc
    cA
    cB
    c.or
    cK
    @24
    @25
    cdlemk1.b
    cdlemk1.j
    cdlemk1.a
    hlatjcl
    syl3anc
    cB
    cK
    c.le
    c.an
    @21
    @22
    @26
    cdlemk1.b
    cdlemk1.l
    cdlemk1.m
    latlem12
    syl13anc
    mpbi2and
end
