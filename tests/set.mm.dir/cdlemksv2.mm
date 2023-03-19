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
include "cv.mm"
include "crio.mm"
include "simp13.mm"
include "cdlemksv.mm"
include "syl.mm"
include "eqcomd.mm"
include "wreu.mm"
include "wb.mm"
include "cdlemksel.mm"
include "simp11.mm"
include "simp22.mm"
include "simp1.mm"
include "simp21.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "simp11l.mm"
include "simp22l.mm"
include "simpld.mm"
include "hlatlej2.mm"
include "simp23.mm"
include "oveq2d.mm"
include "trljat1.mm"
include "eqtr2d.mm"
include "breqtrd.mm"
include "simp31.mm"
include "simp32.mm"
include "simp33.mm"
include "necomd.mm"
include "eqid.mm"
include "cdlemh.mm"
include "syl133anc.mm"
include "cdleme.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfriota1.mm"
include "nfmpt.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfeq1.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "riota2f.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem cdlemksv2
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  assume cdlemk.b: |- B = ( Base ` K )
  assume cdlemk.l: |- .<_ = ( le ` K )
  assume cdlemk.j: |- .\/ = ( join ` K )
  assume cdlemk.a: |- A = ( Atoms ` K )
  assume cdlemk.h: |- H = ( LHyp ` K )
  assume cdlemk.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk.m: |- ./\ = ( meet ` K )
  assume cdlemk.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )

  disjoint ./\ f
  disjoint .\/ f
  disjoint F f
  disjoint f i
  disjoint G f
  disjoint G i
  disjoint N f
  disjoint P f
  disjoint R f
  disjoint T f
  disjoint W f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ i
  disjoint A i
  disjoint F i
  disjoint H i
  disjoint K i
  disjoint N i
  disjoint P i
  disjoint R i
  disjoint T i
  disjoint W i
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ ( R ` G ) =/= ( R ` F ) ) ) -> ( ( S ` G ) ` P ) = ( ( P .\/ ( R ` G ) ) ./\ ( ( N ` P ) .\/ ( R ` ( G o. `' F ) ) ) ) )

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
    cG
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
    cG
    @14
    wne
    #
    cG
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
    cG
    cS
    cfv
    #
    cfv
    #
    cP
    @17
    c.or
    co
    cP
    cN
    cfv
    #
    cG
    cF
    ccnv
    #
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    #
    wceq
    #
    cP
    vi
    cv
    #
    cfv
    #
    @25
    wceq
    #
    vi
    cT
    crio
    #
    @21
    wceq
    #
    @20
    @21
    @30
    @20
    @4
    @21
    @30
    wceq
    @2
    @3
    @4
    @13
    @19
    simp13
    cA
    cB
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    cdlemk.m
    cdlemk.s
    cdlemksv
    syl
    eqcomd
    @20
    @21
    cT
    wcel
    @29
    vi
    cT
    wreu
    #
    @26
    @31
    wb
    cA
    cB
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    cdlemk.m
    cdlemk.s
    cdlemksel
    @20
    @2
    @9
    @25
    cA
    wcel
    @25
    cW
    c.le
    wbr
    wn
    wa
    #
    @32
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
    simp22
    #
    @20
    @5
    @9
    @23
    cA
    wcel
    #
    @23
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @23
    cP
    @10
    c.or
    co
    #
    c.le
    wbr
    @15
    @16
    @10
    @17
    wne
    @33
    @5
    @13
    @19
    simp1
    @35
    @20
    @2
    @6
    @9
    @38
    @34
    @5
    @6
    @9
    @12
    @19
    simp21
    #
    @35
    cA
    cP
    cT
    cN
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrnel
    syl3anc
    #
    @20
    @23
    cP
    @23
    c.or
    co
    #
    @39
    c.le
    @20
    @0
    @7
    @36
    @23
    @42
    c.le
    wbr
    @0
    @1
    @3
    @4
    @13
    @19
    simp11l
    @7
    @8
    @6
    @12
    @5
    @19
    simp22l
    @20
    @36
    @37
    @41
    simpld
    cA
    cP
    @23
    c.or
    cK
    c.le
    cdlemk.l
    cdlemk.j
    cdlemk.a
    hlatlej2
    syl3anc
    @20
    @39
    cP
    @11
    c.or
    co
    #
    @42
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
    @43
    @42
    wceq
    @34
    @40
    @35
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
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trljat1
    syl3anc
    eqtr2d
    breqtrd
    @5
    @13
    @15
    @16
    @18
    simp31
    @5
    @13
    @15
    @16
    @18
    simp32
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
    cB
    cP
    @23
    cR
    @25
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.m
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    @25
    eqid
    cdlemh
    syl133anc
    cA
    cP
    @25
    cT
    vi
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdleme
    syl3anc
    @29
    @26
    vi
    cT
    @21
    vi
    cG
    cS
    vi
    cS
    vf
    cT
    @28
    cP
    vf
    cv
    #
    cR
    cfv
    c.or
    co
    @23
    @44
    @24
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    wceq
    #
    vi
    cT
    crio
    #
    cmpt
    cdlemk.s
    vi
    vf
    cT
    @46
    vi
    cT
    nfcv
    @45
    vi
    cT
    nfriota1
    nfmpt
    nfcxfr
    vi
    cG
    nfcv
    nffv
    #
    vi
    @22
    @25
    vi
    cP
    @21
    @47
    vi
    cP
    nfcv
    nffv
    nfeq1
    @27
    @21
    wceq
    @28
    @22
    @25
    cP
    @27
    @21
    fveq1
    eqeq1d
    riota2f
    syl2anc
    mpbird
end
