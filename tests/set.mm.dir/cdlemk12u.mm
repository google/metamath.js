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
include "simp212.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "simp23.mm"
include "simp213.mm"
include "simp12.mm"
include "simp13.mm"
include "simp211.mm"
include "simp331.mm"
include "simp333.mm"
include "necomd.mm"
include "jca.mm"
include "simp311.mm"
include "simp32l.mm"
include "simp312.mm"
include "3jca.mm"
include "simp22.mm"
include "cdlemkuat.mm"
include "syl333anc.mm"
include "simp32r.mm"
include "trlcocnvat.mm"
include "syl121anc.mm"
include "simp332.mm"
include "simp313.mm"
include "cdlemkuv2.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "trlnidat.mm"
include "hlatjcl.mm"
include "simp1.mm"
include "cdlemkoatnle.mm"
include "simpld.mm"
include "syl113anc.mm"
include "latmle1.mm"
include "eqbrtrd.mm"
include "trljat1.mm"
include "breqtrd.mm"
include "simp2.mm"
include "simp31.mm"
include "simp33.mm"
include "eqid.mm"
include "cdlemk11u.mm"
include "hlatlej2.mm"
include "cdlemkuel.mm"
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

theorem cdlemk12u
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let ve: setvar e
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
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
  assume cdlemk1.u: |- U = ( e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( O ` P ) .\/ ( R ` ( e o. `' D ) ) ) ) ) )

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
  disjoint ./\ e
  disjoint .\/ e
  disjoint D e
  disjoint e j
  disjoint G e
  disjoint G j
  disjoint O e
  disjoint P e
  disjoint R e
  disjoint T e
  disjoint W e
  disjoint ./\ j
  disjoint .<_ j
  disjoint .\/ j
  disjoint A j
  disjoint D j
  disjoint F j
  disjoint H j
  disjoint K j
  disjoint N j
  disjoint O j
  disjoint P j
  disjoint R j
  disjoint T j
  disjoint W j
  disjoint F e
  disjoint X e
  disjoint X j
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( ( N e. T /\ G e. T /\ X e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ G =/= ( _I |` B ) ) /\ ( X =/= ( _I |` B ) /\ ( R ` G ) =/= ( R ` X ) ) /\ ( ( R ` D ) =/= ( R ` F ) /\ ( R ` G ) =/= ( R ` D ) /\ ( R ` X ) =/= ( R ` D ) ) ) ) -> ( ( U ` G ) ` P ) = ( ( P .\/ ( G ` P ) ) ./\ ( ( ( U ` X ) ` P ) .\/ ( R ` ( X o. `' G ) ) ) ) )

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
    cG
    cT
    wcel
    #
    cX
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
    cD
    @16
    wne
    #
    cG
    @16
    wne
    #
    w3a
    #
    cX
    @16
    wne
    #
    cG
    cR
    cfv
    #
    cX
    cR
    cfv
    #
    wne
    #
    wa
    #
    cD
    cR
    cfv
    #
    @13
    wne
    #
    @22
    @26
    wne
    #
    @23
    @26
    wne
    #
    w3a
    #
    w3a
    #
    w3a
    #
    @0
    @10
    cP
    cG
    cfv
    #
    cA
    wcel
    #
    cP
    cX
    cU
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
    cU
    cfv
    cfv
    #
    cA
    wcel
    #
    @42
    cP
    @33
    c.or
    co
    #
    c.le
    wbr
    @42
    @36
    @40
    c.or
    co
    #
    c.le
    wbr
    #
    @44
    @45
    wne
    #
    @42
    @44
    @45
    c.an
    co
    wceq
    @0
    @1
    @3
    @4
    @15
    @31
    simp11l
    #
    @10
    @11
    @9
    @14
    @5
    @31
    simp22l
    #
    @32
    @2
    @7
    @10
    @34
    @2
    @3
    @4
    @15
    @31
    simp11
    #
    @6
    @7
    @8
    @12
    @14
    @5
    @31
    simp212
    #
    @49
    cA
    cP
    cT
    cG
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
    @32
    @2
    @14
    @8
    @3
    @4
    @6
    @27
    @26
    @23
    wne
    #
    wa
    #
    @17
    @21
    @18
    w3a
    #
    @12
    @37
    @50
    @5
    @9
    @12
    @14
    @31
    simp23
    #
    @6
    @7
    @8
    @12
    @14
    @5
    @31
    simp213
    #
    @2
    @3
    @4
    @15
    @31
    simp12
    #
    @2
    @3
    @4
    @15
    @31
    simp13
    #
    @6
    @7
    @8
    @12
    @14
    @5
    @31
    simp211
    #
    @32
    @27
    @52
    @27
    @28
    @29
    @20
    @25
    @5
    @15
    simp331
    #
    @32
    @23
    @26
    @27
    @28
    @29
    @20
    @25
    @5
    @15
    simp333
    necomd
    jca
    #
    @32
    @17
    @21
    @18
    @17
    @18
    @19
    @25
    @30
    @5
    @15
    simp311
    #
    @21
    @24
    @20
    @30
    @5
    @15
    simp32l
    #
    @17
    @18
    @19
    @25
    @30
    @5
    @15
    simp312
    #
    3jca
    #
    @5
    @9
    @12
    @14
    @31
    simp22
    #
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    cU
    ve
    vf
    vi
    vj
    cF
    cX
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
    cdlemk1.u
    cdlemkuat
    syl333anc
    @32
    @2
    @8
    @7
    @23
    @22
    wne
    @41
    @50
    @56
    @51
    @32
    @22
    @23
    @21
    @24
    @20
    @30
    @5
    @15
    simp32r
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
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlcocnvat
    syl121anc
    #
    @32
    @2
    @14
    @7
    @3
    @4
    @6
    @27
    @26
    @22
    wne
    #
    wa
    #
    @17
    @19
    @18
    w3a
    #
    @12
    @43
    @50
    @55
    @51
    @57
    @58
    @59
    @32
    @27
    @69
    @60
    @32
    @22
    @26
    @27
    @28
    @29
    @20
    @25
    @5
    @15
    simp332
    #
    necomd
    jca
    #
    @32
    @17
    @19
    @18
    @62
    @17
    @18
    @19
    @25
    @30
    @5
    @15
    simp313
    #
    @64
    3jca
    #
    @66
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    cU
    ve
    vf
    vi
    vj
    cF
    cG
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
    cdlemk1.u
    cdlemkuat
    syl333anc
    @32
    @42
    cP
    @22
    c.or
    co
    #
    @44
    c.le
    @32
    @42
    @76
    cP
    cO
    cfv
    #
    cG
    cD
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
    @76
    c.le
    @32
    @2
    @14
    @7
    @3
    @4
    @6
    @70
    @71
    @12
    @42
    @81
    wceq
    @50
    @55
    @51
    @57
    @58
    @59
    @73
    @75
    @66
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    cU
    ve
    vf
    vi
    vj
    cF
    cG
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
    cdlemk1.u
    cdlemkuv2
    syl333anc
    @32
    cK
    clat
    wcel
    #
    @76
    cB
    wcel
    #
    @80
    cB
    wcel
    #
    @81
    @76
    c.le
    wbr
    @32
    @0
    @82
    @48
    cK
    hllat
    syl
    @32
    @0
    @10
    @22
    cA
    wcel
    #
    @83
    @48
    @49
    @32
    @2
    @7
    @19
    @85
    @50
    @51
    @74
    cA
    cB
    cR
    cT
    cG
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
    #
    cA
    cB
    c.or
    cK
    cP
    @22
    cdlemk1.b
    cdlemk1.j
    cdlemk1.a
    hlatjcl
    syl3anc
    @32
    @0
    @77
    cA
    wcel
    #
    @79
    cA
    wcel
    #
    @84
    @48
    @32
    @5
    @6
    @12
    @14
    w3a
    #
    @17
    @18
    @27
    @87
    @5
    @15
    @31
    simp1
    #
    @32
    @6
    @12
    @14
    @59
    @66
    @55
    3jca
    @62
    @64
    @60
    @5
    @89
    @17
    @18
    @27
    w3a
    w3a
    @87
    @77
    cW
    c.le
    wbr
    wn
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
    cdlemkoatnle
    simpld
    syl113anc
    @32
    @2
    @7
    @4
    @28
    @88
    @50
    @51
    @58
    @72
    cA
    cR
    cT
    cG
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
    @77
    @79
    cdlemk1.b
    cdlemk1.j
    cdlemk1.a
    hlatjcl
    syl3anc
    cB
    cK
    c.le
    c.an
    @76
    @80
    cdlemk1.b
    cdlemk1.l
    cdlemk1.m
    latmle1
    syl3anc
    eqbrtrd
    @32
    @2
    @7
    @12
    @76
    @44
    wceq
    @50
    @51
    @66
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
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trljat1
    syl3anc
    #
    breqtrd
    @32
    @5
    @15
    @20
    @21
    @30
    @46
    @90
    @5
    @15
    @31
    simp2
    @5
    @15
    @20
    @25
    @30
    simp31
    @63
    @5
    @15
    @20
    @25
    @30
    simp33
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    cU
    ve
    vf
    vi
    vj
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    @33
    cP
    cX
    cfv
    c.or
    co
    @79
    cX
    @78
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
    cdlemk1.u
    @92
    eqid
    cdlemk11u
    syl113anc
    @32
    @22
    @44
    c.le
    wbr
    @22
    @45
    c.le
    wbr
    wn
    #
    @47
    @32
    @22
    @76
    @44
    c.le
    @32
    @0
    @10
    @85
    @22
    @76
    c.le
    wbr
    @48
    @49
    @86
    cA
    cP
    @22
    c.or
    cK
    c.le
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    hlatlej2
    syl3anc
    @91
    breqtrd
    @32
    @2
    @37
    @36
    cW
    c.le
    wbr
    wn
    wa
    #
    @40
    @22
    wne
    @41
    @40
    cW
    c.le
    wbr
    #
    @85
    @22
    cW
    c.le
    wbr
    #
    @93
    @50
    @32
    @2
    @35
    cT
    wcel
    #
    @12
    @94
    @50
    @32
    @2
    @14
    @8
    @3
    @4
    @6
    @53
    @54
    @12
    @97
    @50
    @55
    @56
    @57
    @58
    @59
    @61
    @65
    @66
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    cU
    ve
    vf
    vi
    vj
    cF
    cX
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
    cdlemk1.u
    cdlemkuel
    syl333anc
    @66
    cA
    cP
    cT
    @35
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    ltrnel
    syl3anc
    @32
    @38
    cX
    ccom
    #
    cR
    cfv
    #
    @38
    cR
    cfv
    #
    @40
    @22
    @32
    @100
    @99
    @32
    @2
    @38
    cT
    wcel
    #
    @8
    @100
    @23
    wne
    @21
    @100
    @99
    wne
    @50
    @32
    @2
    @7
    @101
    @50
    @51
    cT
    cG
    cH
    cK
    cW
    cdlemk1.h
    cdlemk1.t
    ltrncnv
    syl2anc
    #
    @56
    @32
    @100
    @22
    @23
    @32
    @2
    @7
    @100
    @22
    wceq
    @50
    @51
    cR
    cT
    cG
    cH
    cK
    cW
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlcnv
    syl2anc
    #
    @67
    eqnetrd
    @63
    cB
    cR
    cT
    @38
    cX
    cH
    cK
    cW
    cdlemk1.b
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlcone
    syl122anc
    necomd
    @32
    @98
    @39
    cR
    @32
    @2
    @101
    @8
    @98
    @39
    wceq
    @50
    @102
    @56
    cT
    @38
    cX
    cH
    cK
    cW
    cdlemk1.h
    cdlemk1.t
    ltrncom
    syl3anc
    fveq2d
    @103
    3netr3d
    @68
    @32
    @2
    @39
    cT
    wcel
    #
    @95
    @50
    @32
    @2
    @8
    @101
    @104
    @50
    @56
    @102
    cT
    cX
    @38
    cH
    cK
    cW
    cdlemk1.h
    cdlemk1.t
    ltrnco
    syl3anc
    cR
    cT
    @39
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlle
    syl2anc
    @86
    @32
    @2
    @7
    @96
    @50
    @51
    cR
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlle
    syl2anc
    cA
    @36
    @40
    cH
    c.or
    cK
    c.le
    @22
    cW
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    cdlemk1.h
    lhp2atnle
    syl322anc
    @22
    @44
    @45
    c.le
    nbrne1
    syl2anc
    cA
    cP
    @33
    @36
    @40
    @42
    c.or
    cK
    c.le
    c.an
    cdlemk1.l
    cdlemk1.j
    cdlemk1.m
    cdlemk1.a
    2atm
    syl333anc
end
