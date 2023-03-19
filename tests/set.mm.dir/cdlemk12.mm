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
include "ccnv.mm"
include "ccom.mm"
include "co.mm"
include "simp11l.mm"
include "simp22l.mm"
include "simp11.mm"
include "simp13.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "simp12.mm"
include "simp21r.mm"
include "3jca.mm"
include "simp21l.mm"
include "simp22.mm"
include "simp23.mm"
include "simp311.mm"
include "simp313.mm"
include "simp32r.mm"
include "cdlemksat.mm"
include "syl113anc.mm"
include "simp33.mm"
include "necomd.mm"
include "trlcocnvat.mm"
include "syl121anc.mm"
include "simp1.mm"
include "simp312.mm"
include "simp32l.mm"
include "cdlemksv2.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "trlnidat.mm"
include "hlatjcl.mm"
include "latmle1.mm"
include "eqbrtrd.mm"
include "trljat1.mm"
include "breqtrd.mm"
include "simp2.mm"
include "simp31.mm"
include "eqid.mm"
include "cdlemk11.mm"
include "hlatlej2.mm"
include "cdlemksel.mm"
include "ltrnel.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "trlcnv.mm"
include "eqnetrd.mm"
include "trlcone.mm"
include "syl122anc.mm"
include "ltrncom.mm"
include "fveq2d.mm"
include "3netr3d.mm"
include "ltrnco.mm"
include "trlle.mm"
include "lhp2atnle.mm"
include "syl322anc.mm"
include "nbrne1.mm"
include "2atm.mm"
include "syl333anc.mm"

theorem cdlemk12
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
  let cX: class X
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
  disjoint X f
  disjoint X i
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) /\ ( ( N e. T /\ X e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ X =/= ( _I |` B ) ) /\ ( ( R ` G ) =/= ( R ` F ) /\ ( R ` X ) =/= ( R ` F ) ) /\ ( R ` G ) =/= ( R ` X ) ) ) -> ( ( S ` G ) ` P ) = ( ( P .\/ ( G ` P ) ) ./\ ( ( ( S ` X ) ` P ) .\/ ( R ` ( X o. `' G ) ) ) ) )

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
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
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
    @15
    wne
    #
    cX
    @15
    wne
    #
    w3a
    #
    cG
    cR
    cfv
    #
    @12
    wne
    #
    cX
    cR
    cfv
    #
    @12
    wne
    #
    wa
    #
    @20
    @22
    wne
    #
    w3a
    #
    w3a
    #
    @0
    @9
    cP
    cG
    cfv
    #
    cA
    wcel
    #
    cP
    cX
    cS
    cfv
    #
    cfv
    #
    cA
    wcel
    #
    cX
    cG
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    cA
    wcel
    #
    cP
    cG
    cS
    cfv
    cfv
    #
    cA
    wcel
    #
    @37
    cP
    @28
    c.or
    co
    #
    c.le
    wbr
    @37
    @31
    @35
    c.or
    co
    #
    c.le
    wbr
    #
    @39
    @40
    wne
    #
    @37
    @39
    @40
    c.an
    co
    wceq
    @0
    @1
    @3
    @4
    @14
    @26
    simp11l
    #
    @9
    @10
    @8
    @13
    @5
    @26
    simp22l
    #
    @27
    @2
    @4
    @9
    @29
    @2
    @3
    @4
    @14
    @26
    simp11
    #
    @2
    @3
    @4
    @14
    @26
    simp13
    #
    @44
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
    @27
    @2
    @3
    @7
    w3a
    #
    @6
    @11
    @13
    w3a
    #
    @16
    @18
    @23
    @32
    @27
    @2
    @3
    @7
    @45
    @2
    @3
    @4
    @14
    @26
    simp12
    #
    @6
    @7
    @11
    @13
    @5
    @26
    simp21r
    #
    3jca
    #
    @27
    @6
    @11
    @13
    @6
    @7
    @11
    @13
    @5
    @26
    simp21l
    #
    @5
    @8
    @11
    @13
    @26
    simp22
    #
    @5
    @8
    @11
    @13
    @26
    simp23
    3jca
    #
    @16
    @17
    @18
    @24
    @25
    @5
    @14
    simp311
    #
    @16
    @17
    @18
    @24
    @25
    @5
    @14
    simp313
    #
    @21
    @23
    @19
    @25
    @5
    @14
    simp32r
    #
    cA
    cB
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cX
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
    cdlemksat
    syl113anc
    @27
    @2
    @7
    @4
    @22
    @20
    wne
    @36
    @45
    @50
    @46
    @27
    @20
    @22
    @5
    @14
    @19
    @24
    @25
    simp33
    #
    necomd
    cA
    cR
    cT
    cX
    cG
    cH
    cK
    cW
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcocnvat
    syl121anc
    #
    @27
    @5
    @48
    @16
    @17
    @21
    @38
    @5
    @14
    @26
    simp1
    #
    @54
    @55
    @16
    @17
    @18
    @24
    @25
    @5
    @14
    simp312
    #
    @21
    @23
    @19
    @25
    @5
    @14
    simp32l
    #
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
    cdlemksat
    syl113anc
    @27
    @37
    cP
    @20
    c.or
    co
    #
    @39
    c.le
    @27
    @37
    @63
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
    #
    c.or
    co
    #
    c.an
    co
    #
    @63
    c.le
    @27
    @5
    @48
    @16
    @17
    @21
    @37
    @68
    wceq
    @60
    @54
    @55
    @61
    @62
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
    cdlemksv2
    syl113anc
    @27
    cK
    clat
    wcel
    #
    @63
    cB
    wcel
    #
    @67
    cB
    wcel
    #
    @68
    @63
    c.le
    wbr
    @27
    @0
    @69
    @43
    cK
    hllat
    syl
    @27
    @0
    @9
    @20
    cA
    wcel
    #
    @70
    @43
    @44
    @27
    @2
    @4
    @17
    @72
    @45
    @46
    @61
    cA
    cB
    cR
    cT
    cG
    cH
    cK
    cW
    cdlemk.b
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlnidat
    syl3anc
    #
    cA
    cB
    c.or
    cK
    cP
    @20
    cdlemk.b
    cdlemk.j
    cdlemk.a
    hlatjcl
    syl3anc
    @27
    @0
    @64
    cA
    wcel
    #
    @66
    cA
    wcel
    #
    @71
    @43
    @27
    @2
    @6
    @9
    @74
    @45
    @52
    @44
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
    ltrnat
    syl3anc
    @27
    @2
    @4
    @3
    @21
    @75
    @45
    @46
    @49
    @62
    cA
    cR
    cT
    cG
    cF
    cH
    cK
    cW
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcocnvat
    syl121anc
    cA
    cB
    c.or
    cK
    @64
    @66
    cdlemk.b
    cdlemk.j
    cdlemk.a
    hlatjcl
    syl3anc
    cB
    cK
    c.le
    c.an
    @63
    @67
    cdlemk.b
    cdlemk.l
    cdlemk.m
    latmle1
    syl3anc
    eqbrtrd
    @27
    @2
    @4
    @11
    @63
    @39
    wceq
    @45
    @46
    @53
    cA
    cP
    cR
    cT
    cG
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
    #
    breqtrd
    @27
    @5
    @14
    @19
    @21
    @23
    @41
    @60
    @5
    @14
    @26
    simp2
    @5
    @14
    @19
    @24
    @25
    simp31
    @62
    @57
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
    @28
    cP
    cX
    cfv
    c.or
    co
    @66
    cX
    @65
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    #
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
    cdlemk.s
    @77
    eqid
    cdlemk11
    syl113anc
    @27
    @20
    @39
    c.le
    wbr
    @20
    @40
    c.le
    wbr
    wn
    #
    @42
    @27
    @20
    @63
    @39
    c.le
    @27
    @0
    @9
    @72
    @20
    @63
    c.le
    wbr
    @43
    @44
    @73
    cA
    cP
    @20
    c.or
    cK
    c.le
    cdlemk.l
    cdlemk.j
    cdlemk.a
    hlatlej2
    syl3anc
    @76
    breqtrd
    @27
    @2
    @32
    @31
    cW
    c.le
    wbr
    wn
    wa
    #
    @35
    @20
    wne
    @36
    @35
    cW
    c.le
    wbr
    #
    @72
    @20
    cW
    c.le
    wbr
    #
    @78
    @45
    @27
    @2
    @30
    cT
    wcel
    #
    @11
    @79
    @45
    @27
    @47
    @48
    @16
    @18
    @23
    @82
    @51
    @54
    @55
    @56
    @57
    cA
    cB
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cX
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
    syl113anc
    @53
    cA
    cP
    cT
    @30
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
    @27
    @33
    cX
    ccom
    #
    cR
    cfv
    #
    @33
    cR
    cfv
    #
    @35
    @20
    @27
    @85
    @84
    @27
    @2
    @33
    cT
    wcel
    #
    @7
    @85
    @22
    wne
    @18
    @85
    @84
    wne
    @45
    @27
    @2
    @4
    @86
    @45
    @46
    cT
    cG
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrncnv
    syl2anc
    #
    @50
    @27
    @85
    @20
    @22
    @27
    @2
    @4
    @85
    @20
    wceq
    @45
    @46
    cR
    cT
    cG
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcnv
    syl2anc
    #
    @58
    eqnetrd
    @56
    cB
    cR
    cT
    @33
    cX
    cH
    cK
    cW
    cdlemk.b
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcone
    syl122anc
    necomd
    @27
    @83
    @34
    cR
    @27
    @2
    @86
    @7
    @83
    @34
    wceq
    @45
    @87
    @50
    cT
    @33
    cX
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrncom
    syl3anc
    fveq2d
    @88
    3netr3d
    @59
    @27
    @2
    @34
    cT
    wcel
    #
    @80
    @45
    @27
    @2
    @7
    @86
    @89
    @45
    @50
    @87
    cT
    cX
    @33
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrnco
    syl3anc
    cR
    cT
    @34
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
    @73
    @27
    @2
    @4
    @81
    @45
    @46
    cR
    cT
    cG
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
    @31
    @35
    cH
    c.or
    cK
    c.le
    @20
    cW
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    lhp2atnle
    syl322anc
    @20
    @39
    @40
    c.le
    nbrne1
    syl2anc
    cA
    cP
    @28
    @31
    @35
    @37
    c.or
    cK
    c.le
    c.an
    cdlemk.l
    cdlemk.j
    cdlemk.m
    cdlemk.a
    2atm
    syl333anc
end
