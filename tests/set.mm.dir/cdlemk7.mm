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
include "simp1.mm"
include "simp2.mm"
include "simp311.mm"
include "simp312.mm"
include "simp32.mm"
include "simp33.mm"
include "jca.mm"
include "cdlemk6.mm"
include "syl113anc.mm"
include "simp21l.mm"
include "simp22.mm"
include "simp23.mm"
include "3jca.mm"
include "cdlemksv2.mm"
include "simp11.mm"
include "simp13.mm"
include "trljat1.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp12.mm"
include "simp21r.mm"
include "simp313.mm"
include "cdlemksat.mm"
include "atbase.mm"
include "simp11r.mm"
include "simp22l.mm"
include "cdlemkvcl.mm"
include "syl231anc.mm"
include "latjcom.mm"
include "a1i.mm"
include "ltrnat.mm"
include "hlatjcom.mm"
include "eqtr4d.mm"
include "trlcocnvat.mm"
include "oveq12d.mm"
include "3brtr4d.mm"

theorem cdlemk7
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
  let cV: class V
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
  assume cdlemk.v: |- V = ( ( ( G ` P ) .\/ ( X ` P ) ) ./\ ( ( R ` ( G o. `' F ) ) .\/ ( R ` ( X o. `' F ) ) ) )

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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) /\ ( ( N e. T /\ X e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ X =/= ( _I |` B ) ) /\ ( R ` G ) =/= ( R ` F ) /\ ( R ` X ) =/= ( R ` F ) ) ) -> ( ( S ` G ) ` P ) .<_ ( ( ( S ` X ) ` P ) .\/ V ) )

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
    @26
    cP
    cX
    cfv
    #
    c.or
    co
    @30
    cX
    @29
    ccom
    cR
    cfv
    #
    c.or
    co
    c.an
    co
    #
    @33
    cP
    c.or
    co
    #
    @34
    @28
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
    cS
    cfv
    cfv
    #
    cP
    cX
    cS
    cfv
    cfv
    #
    cV
    c.or
    co
    #
    c.le
    @25
    @5
    @14
    @16
    @17
    @21
    @23
    wa
    @32
    @39
    c.le
    wbr
    @5
    @14
    @24
    simp1
    #
    @5
    @14
    @24
    simp2
    @16
    @17
    @18
    @21
    @23
    @5
    @14
    simp311
    #
    @16
    @17
    @18
    @21
    @23
    @5
    @14
    simp312
    #
    @25
    @21
    @23
    @5
    @14
    @19
    @21
    @23
    simp32
    #
    @5
    @14
    @19
    @21
    @23
    simp33
    #
    jca
    cA
    cB
    cP
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
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
    cdlemk6
    syl113anc
    @25
    @40
    cP
    @20
    c.or
    co
    #
    @31
    c.an
    co
    #
    @32
    @25
    @5
    @6
    @11
    @13
    w3a
    #
    @16
    @17
    @21
    @40
    @49
    wceq
    @43
    @25
    @6
    @11
    @13
    @6
    @7
    @11
    @13
    @5
    @24
    simp21l
    #
    @5
    @8
    @11
    @13
    @24
    simp22
    #
    @5
    @8
    @11
    @13
    @24
    simp23
    3jca
    #
    @44
    @45
    @46
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
    @25
    @48
    @27
    @31
    c.an
    @25
    @2
    @4
    @11
    @48
    @27
    wceq
    @2
    @3
    @4
    @14
    @24
    simp11
    #
    @2
    @3
    @4
    @14
    @24
    simp13
    #
    @52
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
    oveq1d
    eqtrd
    @25
    @42
    cV
    @41
    c.or
    co
    #
    @39
    @25
    cK
    clat
    wcel
    #
    @41
    cB
    wcel
    #
    cV
    cB
    wcel
    #
    @42
    @56
    wceq
    @25
    @0
    @57
    @0
    @1
    @3
    @4
    @14
    @24
    simp11l
    #
    cK
    hllat
    syl
    @25
    @41
    cA
    wcel
    #
    @58
    @25
    @2
    @3
    @7
    w3a
    #
    @50
    @16
    @18
    @23
    @61
    @25
    @2
    @3
    @7
    @54
    @2
    @3
    @4
    @14
    @24
    simp12
    #
    @6
    @7
    @11
    @13
    @5
    @24
    simp21r
    #
    3jca
    #
    @53
    @44
    @16
    @17
    @18
    @21
    @23
    @5
    @14
    simp313
    #
    @47
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
    cA
    cB
    @41
    cK
    cdlemk.b
    cdlemk.a
    atbase
    syl
    @25
    @0
    @1
    @3
    @4
    @7
    @9
    @59
    @60
    @0
    @1
    @3
    @4
    @14
    @24
    simp11r
    @63
    @55
    @64
    @9
    @10
    @8
    @13
    @5
    @24
    simp22l
    #
    cA
    cB
    cP
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cV
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
    cdlemk.v
    cdlemkvcl
    syl231anc
    cB
    c.or
    cK
    @41
    cV
    cdlemk.b
    cdlemk.j
    latjcom
    syl3anc
    @25
    cV
    @35
    @41
    @38
    c.or
    cV
    @35
    wceq
    @25
    cdlemk.v
    a1i
    @25
    @41
    cP
    @22
    c.or
    co
    #
    @28
    @34
    c.or
    co
    #
    c.an
    co
    #
    @38
    @25
    @62
    @50
    @16
    @18
    @23
    @41
    @70
    wceq
    @65
    @53
    @44
    @66
    @47
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
    cdlemksv2
    syl113anc
    @25
    @68
    @36
    @69
    @37
    c.an
    @25
    @68
    cP
    @33
    c.or
    co
    #
    @36
    @25
    @2
    @7
    @11
    @68
    @71
    wceq
    @54
    @64
    @52
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
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trljat1
    syl3anc
    @25
    @0
    @33
    cA
    wcel
    #
    @9
    @36
    @71
    wceq
    @60
    @25
    @2
    @7
    @9
    @72
    @54
    @64
    @67
    cA
    cP
    cT
    cX
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
    @67
    cA
    c.or
    cK
    @33
    cP
    cdlemk.j
    cdlemk.a
    hlatjcom
    syl3anc
    eqtr4d
    @25
    @0
    @28
    cA
    wcel
    #
    @34
    cA
    wcel
    #
    @69
    @37
    wceq
    @60
    @25
    @2
    @6
    @9
    @73
    @54
    @51
    @67
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
    @25
    @2
    @7
    @3
    wa
    @23
    @74
    @54
    @25
    @7
    @3
    @64
    @63
    jca
    @47
    cA
    cR
    cT
    cX
    cF
    cH
    cK
    cW
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcocnvat
    syl3anc
    cA
    c.or
    cK
    @28
    @34
    cdlemk.j
    cdlemk.a
    hlatjcom
    syl3anc
    oveq12d
    eqtrd
    oveq12d
    eqtrd
    3brtr4d
end
