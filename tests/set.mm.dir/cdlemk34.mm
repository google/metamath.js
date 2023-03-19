include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "ccnv.mm"
include "ccom.mm"
include "wb.mm"
include "fveq1.mm"
include "simpll1.mm"
include "simplr1.mm"
include "simpl1.mm"
include "simpl3r.mm"
include "simp22l.mm"
include "adantr.mm"
include "3jca.mm"
include "simp21l.mm"
include "simpr2.mm"
include "simpl23.mm"
include "simpr32.mm"
include "simpr33.mm"
include "jca.mm"
include "simp21r.mm"
include "simp22r.mm"
include "simpr31.mm"
include "simpl3l.mm"
include "cdlemkuel-3.mm"
include "syl113anc.mm"
include "simpr.mm"
include "cdlemd.mm"
include "syl311anc.mm"
include "ex.mm"
include "impbid2.mm"
include "simp1.mm"
include "simp3r.mm"
include "cdlemk32.mm"
include "syl123anc.mm"
include "eqeq2d.mm"
include "bitrd.mm"
include "3exp2.mm"
include "imp31.mm"
include "pm5.74d.mm"
include "ralbidva.mm"
include "riotabidva.mm"
include "syl5eq.mm"

theorem cdlemk34
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) /\ N e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) ) -> X = ( iota_ z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) -> ( z ` P ) = ( ( P .\/ ( R ` G ) ) ./\ ( ( ( P .\/ ( R ` b ) ) ./\ ( ( N ` P ) .\/ ( R ` ( b o. `' F ) ) ) ) .\/ ( R ` ( G o. `' b ) ) ) ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
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
    wa
    #
    cG
    cT
    wcel
    #
    cG
    @2
    wne
    #
    wa
    #
    cN
    cT
    wcel
    #
    w3a
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
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    #
    wa
    #
    w3a
    #
    cX
    vb
    cv
    #
    @2
    wne
    #
    @15
    cR
    cfv
    #
    @11
    wne
    #
    @17
    cG
    cR
    cfv
    #
    wne
    #
    w3a
    #
    vz
    cv
    #
    @15
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
    #
    cP
    @19
    c.or
    co
    cP
    @17
    c.or
    co
    cP
    cN
    cfv
    @15
    cF
    ccnv
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    cG
    @15
    ccnv
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
    @14
    @26
    @31
    vz
    cT
    @14
    @22
    cT
    wcel
    #
    wa
    #
    @25
    @30
    vb
    cT
    @33
    @15
    cT
    wcel
    #
    wa
    @21
    @24
    @29
    @14
    @32
    @34
    @21
    @24
    @29
    wb
    #
    wi
    @14
    @32
    @34
    @21
    @35
    @14
    @32
    @34
    @21
    w3a
    #
    wa
    #
    @24
    @27
    cP
    @23
    cfv
    #
    wceq
    #
    @29
    @37
    @24
    @39
    cP
    @22
    @23
    fveq1
    @37
    @39
    @24
    @37
    @39
    wa
    #
    @0
    @32
    @23
    cT
    wcel
    #
    @10
    @39
    @24
    @0
    @9
    @13
    @36
    @39
    simpll1
    @32
    @34
    @21
    @14
    @39
    simplr1
    @40
    @0
    @12
    @5
    w3a
    #
    @1
    @34
    @8
    w3a
    #
    @18
    @20
    wa
    #
    @3
    @6
    @16
    w3a
    #
    @10
    @41
    @37
    @42
    @39
    @37
    @0
    @12
    @5
    @0
    @9
    @13
    @36
    simpl1
    @10
    @12
    @0
    @9
    @36
    simpl3r
    @14
    @5
    @36
    @5
    @6
    @4
    @8
    @0
    @13
    simp22l
    adantr
    #
    3jca
    adantr
    @37
    @43
    @39
    @37
    @1
    @34
    @8
    @14
    @1
    @36
    @1
    @3
    @7
    @8
    @0
    @13
    simp21l
    adantr
    @14
    @32
    @34
    @21
    simpr2
    @4
    @7
    @8
    @0
    @13
    @36
    simpl23
    3jca
    #
    adantr
    @37
    @44
    @39
    @37
    @18
    @20
    @16
    @18
    @20
    @32
    @34
    @14
    simpr32
    @16
    @18
    @20
    @32
    @34
    @14
    simpr33
    jca
    #
    adantr
    @37
    @45
    @39
    @37
    @3
    @6
    @16
    @14
    @3
    @36
    @1
    @3
    @7
    @8
    @0
    @13
    simp21r
    adantr
    #
    @14
    @6
    @36
    @5
    @6
    @4
    @8
    @0
    @13
    simp22r
    adantr
    #
    @16
    @18
    @20
    @32
    @34
    @14
    simpr31
    #
    3jca
    adantr
    @37
    @10
    @39
    @10
    @12
    @0
    @9
    @36
    simpl3l
    #
    adantr
    #
    cA
    cB
    @15
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
    syl113anc
    @53
    @37
    @39
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
    @37
    @38
    @28
    @27
    @37
    @0
    @12
    wa
    #
    @43
    @5
    @44
    @3
    @16
    @6
    w3a
    @10
    @38
    @28
    wceq
    @14
    @54
    @36
    @14
    @0
    @12
    @0
    @9
    @13
    simp1
    @0
    @9
    @10
    @12
    simp3r
    jca
    adantr
    @47
    @46
    @48
    @37
    @3
    @16
    @6
    @49
    @51
    @50
    3jca
    @52
    cA
    cB
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
    vb
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
    cdlemk32
    syl123anc
    eqeq2d
    bitrd
    3exp2
    imp31
    pm5.74d
    ralbidva
    riotabidva
    syl5eq
end
