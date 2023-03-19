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
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "simp1.mm"
include "simp21l.mm"
include "simp21r.mm"
include "simp23.mm"
include "3jca.mm"
include "simp22l.mm"
include "simp22r.mm"
include "simp3r.mm"
include "simp3l.mm"
include "cdlemk26b-3.mm"
include "syl31anc.mm"
include "simp11.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "simp123.mm"
include "simp2r.mm"
include "jca.mm"
include "simp13l.mm"
include "simp13r.mm"
include "simp3l1.mm"
include "simp3r1.mm"
include "simp3r3.mm"
include "necomd.mm"
include "simp3r2.mm"
include "simp3l2.mm"
include "simp3l3.mm"
include "cdlemk27-3.mm"
include "syl332anc.mm"
include "3exp.mm"
include "ralrimivv.mm"
include "weq.mm"
include "neeq1.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "3anbi123d.mm"
include "oveq1.mm"
include "reusv3.mm"
include "biimpd.mm"
include "sylc.mm"

theorem cdlemk28-3
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) /\ N e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) ) -> E. z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) -> z = ( b Y G ) ) )

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
    @15
    cG
    cY
    co
    #
    cT
    wcel
    wa
    vb
    cT
    wrex
    #
    @21
    va
    cv
    #
    @2
    wne
    #
    @24
    cR
    cfv
    #
    @11
    wne
    #
    @26
    @19
    wne
    #
    w3a
    #
    wa
    #
    @22
    @24
    cG
    cY
    co
    #
    wceq
    #
    wi
    #
    va
    cT
    wral
    vb
    cT
    wral
    #
    @21
    vz
    cv
    @22
    wceq
    wi
    vb
    cT
    wral
    vz
    cT
    wrex
    #
    @14
    @0
    @1
    @3
    @8
    w3a
    @5
    @6
    @12
    w3a
    @10
    @23
    @0
    @9
    @13
    simp1
    @14
    @1
    @3
    @8
    @1
    @3
    @7
    @8
    @0
    @13
    simp21l
    #
    @1
    @3
    @7
    @8
    @0
    @13
    simp21r
    #
    @0
    @4
    @7
    @8
    @13
    simp23
    3jca
    @14
    @5
    @6
    @12
    @5
    @6
    @4
    @8
    @0
    @13
    simp22l
    #
    @5
    @6
    @4
    @8
    @0
    @13
    simp22r
    #
    @0
    @9
    @10
    @12
    simp3r
    3jca
    @0
    @9
    @10
    @12
    simp3l
    vb
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
    cdlemk26b-3
    syl31anc
    @14
    @33
    vb
    va
    cT
    cT
    @14
    @15
    cT
    wcel
    #
    @24
    cT
    wcel
    #
    wa
    #
    @30
    @32
    @14
    @42
    @30
    w3a
    #
    @0
    @1
    @40
    @8
    w3a
    @5
    @41
    wa
    @10
    @12
    @3
    @16
    w3a
    @6
    @25
    wa
    @19
    @26
    wne
    #
    @27
    @18
    w3a
    @19
    @17
    wne
    @32
    @0
    @9
    @13
    @42
    @30
    simp11
    @43
    @1
    @40
    @8
    @14
    @42
    @1
    @30
    @36
    3ad2ant1
    @14
    @40
    @41
    @30
    simp2l
    @4
    @7
    @8
    @0
    @13
    @42
    @30
    simp123
    3jca
    @43
    @5
    @41
    @14
    @42
    @5
    @30
    @38
    3ad2ant1
    @14
    @40
    @41
    @30
    simp2r
    jca
    @10
    @12
    @0
    @9
    @42
    @30
    simp13l
    @43
    @12
    @3
    @16
    @10
    @12
    @0
    @9
    @42
    @30
    simp13r
    @14
    @42
    @3
    @30
    @37
    3ad2ant1
    @16
    @18
    @20
    @29
    @14
    @42
    simp3l1
    3jca
    @43
    @6
    @25
    @14
    @42
    @6
    @30
    @39
    3ad2ant1
    @25
    @27
    @28
    @21
    @14
    @42
    simp3r1
    jca
    @43
    @44
    @27
    @18
    @43
    @26
    @19
    @25
    @27
    @28
    @21
    @14
    @42
    simp3r3
    necomd
    @25
    @27
    @28
    @21
    @14
    @42
    simp3r2
    @16
    @18
    @20
    @29
    @14
    @42
    simp3l2
    3jca
    @43
    @17
    @19
    @16
    @18
    @20
    @29
    @14
    @42
    simp3l3
    necomd
    cA
    cB
    @24
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
    cdlemk27-3
    syl332anc
    3exp
    ralrimivv
    @23
    @34
    @35
    @21
    @29
    vz
    vb
    va
    cT
    cT
    @22
    @31
    vb
    va
    weq
    #
    @16
    @25
    @18
    @27
    @20
    @28
    @15
    @24
    @2
    neeq1
    @45
    @17
    @26
    @11
    @15
    @24
    cR
    fveq2
    #
    neeq1d
    @45
    @17
    @26
    @19
    @46
    neeq1d
    3anbi123d
    @15
    @24
    cG
    cY
    oveq1
    reusv3
    biimpd
    sylc
end
