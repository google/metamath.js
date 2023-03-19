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
include "simp31.mm"
include "simp33.mm"
include "jca.mm"
include "cdlemk6u.mm"
include "syld3an3.mm"
include "simp11l.mm"
include "simp11r.mm"
include "simp23.mm"
include "simp212.mm"
include "simp12.mm"
include "simp13.mm"
include "simp211.mm"
include "3jca.mm"
include "simp331.mm"
include "simp332.mm"
include "necomd.mm"
include "simp311.mm"
include "simp313.mm"
include "simp312.mm"
include "simp22.mm"
include "cdlemkuv2.mm"
include "syl313anc.mm"
include "trljat1.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp213.mm"
include "simp333.mm"
include "simp32.mm"
include "cdlemkuat.mm"
include "atbase.mm"
include "simp22l.mm"
include "cdlemkvcl.mm"
include "syl231anc.mm"
include "latjcom.mm"
include "a1i.mm"
include "ltrnat.mm"
include "hlatjcom.mm"
include "eqtr4d.mm"
include "simp1.mm"
include "cdlemkoatnle.mm"
include "simpld.mm"
include "trlcocnvat.mm"
include "oveq12d.mm"
include "3brtr4d.mm"

theorem cdlemk7u
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
  let cV: class V
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
  assume cdlemk1.v: |- V = ( ( ( G ` P ) .\/ ( X ` P ) ) ./\ ( ( R ` ( G o. `' D ) ) .\/ ( R ` ( X o. `' D ) ) ) )

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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( ( N e. T /\ G e. T /\ X e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ G =/= ( _I |` B ) ) /\ X =/= ( _I |` B ) /\ ( ( R ` D ) =/= ( R ` F ) /\ ( R ` G ) =/= ( R ` D ) /\ ( R ` X ) =/= ( R ` D ) ) ) ) -> ( ( U ` G ) ` P ) .<_ ( ( ( U ` X ) ` P ) .\/ V ) )

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
    cD
    cR
    cfv
    #
    @13
    wne
    #
    cG
    cR
    cfv
    #
    @22
    wne
    #
    cX
    cR
    cfv
    #
    @22
    wne
    #
    w3a
    #
    w3a
    #
    w3a
    #
    cP
    cP
    cG
    cfv
    #
    c.or
    co
    #
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
    @31
    cP
    cX
    cfv
    #
    c.or
    co
    @35
    cX
    @34
    ccom
    cR
    cfv
    #
    c.or
    co
    c.an
    co
    #
    @38
    cP
    c.or
    co
    #
    @39
    @33
    c.or
    co
    #
    c.an
    co
    #
    c.or
    co
    #
    cP
    cG
    cU
    cfv
    cfv
    #
    cP
    cX
    cU
    cfv
    cfv
    #
    cV
    c.or
    co
    #
    c.le
    @5
    @15
    @29
    @20
    @28
    wa
    @37
    @44
    c.le
    wbr
    @30
    @20
    @28
    @5
    @15
    @20
    @21
    @28
    simp31
    @5
    @15
    @20
    @21
    @28
    simp33
    jca
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
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
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
    cdlemk6u
    syld3an3
    @30
    @45
    cP
    @24
    c.or
    co
    #
    @36
    c.an
    co
    #
    @37
    @30
    @2
    @14
    @7
    @3
    @4
    @6
    w3a
    #
    @23
    @22
    @24
    wne
    #
    wa
    @17
    @19
    @18
    w3a
    @12
    @45
    @49
    wceq
    @30
    @0
    @1
    @0
    @1
    @3
    @4
    @15
    @29
    simp11l
    #
    @0
    @1
    @3
    @4
    @15
    @29
    simp11r
    #
    jca
    #
    @5
    @9
    @12
    @14
    @29
    simp23
    #
    @6
    @7
    @8
    @12
    @14
    @5
    @29
    simp212
    #
    @30
    @3
    @4
    @6
    @2
    @3
    @4
    @15
    @29
    simp12
    @2
    @3
    @4
    @15
    @29
    simp13
    #
    @6
    @7
    @8
    @12
    @14
    @5
    @29
    simp211
    #
    3jca
    #
    @30
    @23
    @51
    @23
    @25
    @27
    @20
    @21
    @5
    @15
    simp331
    #
    @30
    @24
    @22
    @23
    @25
    @27
    @20
    @21
    @5
    @15
    simp332
    necomd
    jca
    @30
    @17
    @19
    @18
    @17
    @18
    @19
    @21
    @28
    @5
    @15
    simp311
    #
    @17
    @18
    @19
    @21
    @28
    @5
    @15
    simp313
    @17
    @18
    @19
    @21
    @28
    @5
    @15
    simp312
    #
    3jca
    @5
    @9
    @12
    @14
    @29
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
    syl313anc
    @30
    @48
    @32
    @36
    c.an
    @30
    @2
    @7
    @12
    @48
    @32
    wceq
    @54
    @56
    @63
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
    oveq1d
    eqtrd
    @30
    @47
    cV
    @46
    c.or
    co
    #
    @44
    @30
    cK
    clat
    wcel
    #
    @46
    cB
    wcel
    #
    cV
    cB
    wcel
    #
    @47
    @64
    wceq
    @30
    @0
    @65
    @52
    cK
    hllat
    syl
    @30
    @46
    cA
    wcel
    #
    @66
    @30
    @2
    @14
    @8
    @50
    @23
    @22
    @26
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
    @68
    @54
    @55
    @6
    @7
    @8
    @12
    @14
    @5
    @29
    simp213
    #
    @59
    @30
    @23
    @69
    @60
    @30
    @26
    @22
    @23
    @25
    @27
    @20
    @21
    @5
    @15
    simp333
    #
    necomd
    jca
    #
    @30
    @17
    @21
    @18
    @61
    @5
    @15
    @20
    @21
    @28
    simp32
    @62
    3jca
    #
    @63
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
    syl313anc
    cA
    cB
    @46
    cK
    cdlemk1.b
    cdlemk1.a
    atbase
    syl
    @30
    @0
    @1
    @4
    @7
    @8
    @10
    @67
    @52
    @53
    @57
    @56
    @72
    @10
    @11
    @9
    @14
    @5
    @29
    simp22l
    #
    cA
    cB
    cP
    cR
    cT
    cD
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cX
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.m
    cdlemk1.v
    cdlemkvcl
    syl231anc
    cB
    c.or
    cK
    @46
    cV
    cdlemk1.b
    cdlemk1.j
    latjcom
    syl3anc
    @30
    cV
    @40
    @46
    @43
    c.or
    cV
    @40
    wceq
    @30
    cdlemk1.v
    a1i
    @30
    @46
    cP
    @26
    c.or
    co
    #
    @33
    @39
    c.or
    co
    #
    c.an
    co
    #
    @43
    @30
    @2
    @14
    @8
    @50
    @70
    @71
    @12
    @46
    @79
    wceq
    @54
    @55
    @72
    @59
    @74
    @75
    @63
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
    cdlemkuv2
    syl313anc
    @30
    @77
    @41
    @78
    @42
    c.an
    @30
    @77
    cP
    @38
    c.or
    co
    #
    @41
    @30
    @2
    @8
    @12
    @77
    @80
    wceq
    @54
    @72
    @63
    cA
    cP
    cR
    cT
    cX
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
    @30
    @0
    @38
    cA
    wcel
    #
    @10
    @41
    @80
    wceq
    @52
    @30
    @2
    @8
    @10
    @81
    @54
    @72
    @76
    cA
    cP
    cT
    cX
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
    @76
    cA
    c.or
    cK
    @38
    cP
    cdlemk1.j
    cdlemk1.a
    hlatjcom
    syl3anc
    eqtr4d
    @30
    @0
    @33
    cA
    wcel
    #
    @39
    cA
    wcel
    #
    @78
    @42
    wceq
    @52
    @30
    @5
    @6
    @12
    @14
    w3a
    #
    @17
    @18
    @23
    w3a
    #
    @82
    @5
    @15
    @29
    simp1
    @30
    @6
    @12
    @14
    @58
    @63
    @55
    3jca
    @30
    @17
    @18
    @23
    @61
    @62
    @60
    3jca
    @5
    @84
    @85
    w3a
    @82
    @33
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
    syl3anc
    @30
    @2
    @8
    @4
    wa
    @27
    @83
    @54
    @30
    @8
    @4
    @72
    @57
    jca
    @73
    cA
    cR
    cT
    cX
    cD
    cH
    cK
    cW
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlcocnvat
    syl3anc
    cA
    c.or
    cK
    @33
    @39
    cdlemk1.j
    cdlemk1.a
    hlatjcom
    syl3anc
    oveq12d
    eqtrd
    oveq12d
    eqtrd
    3brtr4d
end
