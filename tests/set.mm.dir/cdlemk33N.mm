include "chlt.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "wb.mm"
include "fveq1.mm"
include "simpl11.mm"
include "simpl12.mm"
include "jca.mm"
include "simpl31.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp22l.mm"
include "3jca.mm"
include "adantr.mm"
include "simp211.mm"
include "simp32.mm"
include "simp213.mm"
include "simp332.mm"
include "simp333.mm"
include "simp212.mm"
include "simp22r.mm"
include "simp331.mm"
include "simp23.mm"
include "cdlemkuel-3.mm"
include "syl3anc.mm"
include "simpl23.mm"
include "simpr.mm"
include "cdlemd.mm"
include "syl311anc.mm"
include "ex.mm"
include "impbid2.mm"
include "3expia.mm"
include "3expd.mm"
include "imp31.mm"
include "pm5.74d.mm"
include "ralbidva.mm"
include "riotabidva.mm"
include "syl5eq.mm"

theorem cdlemk33N
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
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
  let cW: class W
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vd: setvar d
  let cD: class D
  let cQ: class Q
  let cC: class C
  let vx: setvar x
  let va: setvar a
  assume cdlemk3.b: |- B = ( Base ` K )
  assume cdlemk3.l: |- .<_ = ( le ` K )
  assume cdlemk3.j: |- .\/ = ( join ` K )
  assume cdlemk3.m: |- ./\ = ( meet ` K )
  assume cdlemk3.a: |- A = ( Atoms ` K )
  assume cdlemk3.h: |- H = ( LHyp ` K )
  assume cdlemk3.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk3.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk3.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk3.u1: |- Y = ( d e. T , e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( ( S ` d ) ` P ) .\/ ( R ` ( e o. `' d ) ) ) ) ) )
  assume cdlemk3.x: |- X = ( iota_ z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) -> z = ( b Y G ) ) )

  disjoint d e
  disjoint d f
  disjoint d i
  disjoint ./\ d
  disjoint e f
  disjoint e i
  disjoint ./\ e
  disjoint f i
  disjoint ./\ f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ d
  disjoint .\/ e
  disjoint .\/ f
  disjoint .\/ i
  disjoint A i
  disjoint d j
  disjoint e j
  disjoint f j
  disjoint i j
  disjoint F f
  disjoint F i
  disjoint G d
  disjoint G e
  disjoint G j
  disjoint H i
  disjoint K i
  disjoint N f
  disjoint N i
  disjoint P d
  disjoint P e
  disjoint P f
  disjoint P i
  disjoint R d
  disjoint R e
  disjoint R f
  disjoint R i
  disjoint T d
  disjoint T e
  disjoint T f
  disjoint T i
  disjoint W d
  disjoint W e
  disjoint W f
  disjoint W i
  disjoint b f
  disjoint b i
  disjoint ./\ j
  disjoint .<_ j
  disjoint .\/ j
  disjoint A j
  disjoint F j
  disjoint H j
  disjoint K j
  disjoint N j
  disjoint P j
  disjoint R j
  disjoint b d
  disjoint S d
  disjoint b e
  disjoint S e
  disjoint b j
  disjoint S j
  disjoint S b
  disjoint T j
  disjoint W j
  disjoint F d
  disjoint F e
  disjoint .<_ e
  disjoint G f
  disjoint G i
  disjoint .<_ b
  disjoint A b
  disjoint b z
  disjoint B b
  disjoint B z
  disjoint F b
  disjoint F z
  disjoint G b
  disjoint G z
  disjoint H b
  disjoint K b
  disjoint N b
  disjoint P b
  disjoint R b
  disjoint R z
  disjoint T b
  disjoint T z
  disjoint W b
  disjoint W z
  disjoint Y b
  disjoint Y z
  disjoint d z
  disjoint e z
  disjoint f z
  disjoint i z
  disjoint j z
  disjoint .<_ z
  disjoint A z
  disjoint H z
  disjoint K z
  disjoint N z
  disjoint P z
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint Q d
  disjoint Q e
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C i
  disjoint C j
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint i x
  disjoint j x
  disjoint .<_ x
  disjoint A x
  disjoint B x
  disjoint D x
  disjoint F x
  disjoint G x
  disjoint H x
  disjoint K x
  disjoint N x
  disjoint P x
  disjoint R x
  disjoint T x
  disjoint Y x
  disjoint W x
  disjoint C x
  disjoint a b
  disjoint .<_ a
  disjoint A a
  disjoint a z
  disjoint B a
  disjoint F a
  disjoint G a
  disjoint H a
  disjoint K a
  disjoint N a
  disjoint P a
  disjoint R a
  disjoint T a
  disjoint W a
  disjoint Y a
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a i
  disjoint a j
  assert |- ( ( ( K e. HL /\ W e. H /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F e. T /\ F =/= ( _I |` B ) /\ N e. T ) /\ ( G e. T /\ G =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> X = ( iota_ z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) -> ( z ` P ) = ( ( b Y G ) ` P ) ) ) )

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
    cT
    wcel
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    cN
    cT
    wcel
    #
    w3a
    #
    cG
    cT
    wcel
    #
    cG
    @6
    wne
    #
    wa
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    wa
    #
    cX
    vb
    cv
    #
    @6
    wne
    #
    @16
    cR
    cfv
    #
    @2
    wne
    #
    @18
    cG
    cR
    cfv
    wne
    #
    w3a
    #
    vz
    cv
    #
    @16
    cG
    cY
    co
    #
    wceq
    #
    wi
    #
    vb
    cT
    wral
    #
    vz
    cT
    crio
    @21
    cP
    @22
    cfv
    cP
    @23
    cfv
    wceq
    #
    wi
    #
    vb
    cT
    wral
    #
    vz
    cT
    crio
    cdlemk3.x
    @15
    @26
    @29
    vz
    cT
    @15
    @22
    cT
    wcel
    #
    wa
    #
    @25
    @28
    vb
    cT
    @31
    @16
    cT
    wcel
    #
    wa
    @21
    @24
    @27
    @15
    @30
    @32
    @21
    @24
    @27
    wb
    #
    wi
    @15
    @30
    @32
    @21
    @33
    @4
    @14
    @30
    @32
    @21
    w3a
    #
    @33
    @4
    @14
    @34
    w3a
    #
    @24
    @27
    cP
    @22
    @23
    fveq1
    @35
    @27
    @24
    @35
    @27
    wa
    #
    @0
    @1
    wa
    #
    @30
    @23
    cT
    wcel
    #
    @13
    @27
    @24
    @36
    @0
    @1
    @0
    @1
    @3
    @14
    @34
    @27
    simpl11
    @0
    @1
    @3
    @14
    @34
    @27
    simpl12
    jca
    @30
    @32
    @21
    @4
    @14
    @27
    simpl31
    @36
    @37
    @3
    @10
    w3a
    #
    @5
    @32
    @8
    w3a
    #
    @19
    @20
    wa
    #
    @7
    @11
    @17
    w3a
    #
    @13
    w3a
    #
    @38
    @35
    @39
    @27
    @35
    @37
    @3
    @10
    @35
    @0
    @1
    @0
    @1
    @3
    @14
    @34
    simp11
    @0
    @1
    @3
    @14
    @34
    simp12
    jca
    @0
    @1
    @3
    @14
    @34
    simp13
    @10
    @11
    @9
    @13
    @4
    @34
    simp22l
    3jca
    adantr
    @35
    @40
    @27
    @35
    @5
    @32
    @8
    @5
    @7
    @8
    @12
    @13
    @4
    @34
    simp211
    @4
    @14
    @30
    @32
    @21
    simp32
    @5
    @7
    @8
    @12
    @13
    @4
    @34
    simp213
    3jca
    adantr
    @35
    @43
    @27
    @35
    @41
    @42
    @13
    @35
    @19
    @20
    @17
    @19
    @20
    @30
    @32
    @4
    @14
    simp332
    @17
    @19
    @20
    @30
    @32
    @4
    @14
    simp333
    jca
    @35
    @7
    @11
    @17
    @5
    @7
    @8
    @12
    @13
    @4
    @34
    simp212
    @10
    @11
    @9
    @13
    @4
    @34
    simp22r
    @17
    @19
    @20
    @30
    @32
    @4
    @14
    simp331
    3jca
    @4
    @9
    @12
    @13
    @34
    simp23
    3jca
    adantr
    cA
    cB
    @16
    cP
    cR
    cS
    cT
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
    cW
    cY
    vd
    cdlemk3.b
    cdlemk3.l
    cdlemk3.j
    cdlemk3.m
    cdlemk3.a
    cdlemk3.h
    cdlemk3.t
    cdlemk3.r
    cdlemk3.s
    cdlemk3.u1
    cdlemkuel-3
    syl3anc
    @9
    @12
    @13
    @4
    @34
    @27
    simpl23
    @35
    @27
    simpr
    cA
    cP
    cT
    @22
    @23
    cH
    cK
    c.le
    cW
    cdlemk3.l
    cdlemk3.a
    cdlemk3.h
    cdlemk3.t
    cdlemd
    syl311anc
    ex
    impbid2
    3expia
    3expd
    imp31
    pm5.74d
    ralbidva
    riotabidva
    syl5eq
end
