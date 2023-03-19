include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "co.mm"
include "simp11.mm"
include "simp121.mm"
include "simp122.mm"
include "simp123.mm"
include "simp131.mm"
include "simp133.mm"
include "3jca.mm"
include "simp21.mm"
include "simp221.mm"
include "simp222.mm"
include "simp223.mm"
include "simp231.mm"
include "simp233.mm"
include "simp333.mm"
include "simp332.mm"
include "simp313.mm"
include "simp32l.mm"
include "simp331.mm"
include "cdlemk22-3.mm"
include "syl333anc.mm"
include "simp132.mm"
include "simp232.mm"
include "simp312.mm"
include "simp311.mm"
include "simp32r.mm"
include "eqtr4d.mm"

theorem cdlemk23-3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
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
  let vd: setvar d
  let cQ: class Q
  let vb: setvar b
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
  disjoint D d
  disjoint e j
  disjoint D e
  disjoint f j
  disjoint D f
  disjoint i j
  disjoint D i
  disjoint D j
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
  disjoint S d
  disjoint S e
  disjoint S j
  disjoint T j
  disjoint W j
  disjoint F d
  disjoint F e
  disjoint .<_ e
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C i
  disjoint C j
  disjoint G f
  disjoint G i
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint i x
  disjoint j x
  disjoint Q d
  disjoint Q e
  disjoint b f
  disjoint b i
  disjoint b d
  disjoint b e
  disjoint b j
  disjoint S b
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ D e. T /\ N e. T ) /\ ( G e. T /\ C e. T /\ x e. T ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( ( R ` F ) = ( R ` N ) /\ F =/= ( _I |` B ) /\ D =/= ( _I |` B ) ) /\ ( G =/= ( _I |` B ) /\ C =/= ( _I |` B ) /\ x =/= ( _I |` B ) ) ) /\ ( ( ( R ` G ) =/= ( R ` C ) /\ ( R ` C ) =/= ( R ` F ) /\ ( R ` D ) =/= ( R ` F ) ) /\ ( ( R ` G ) =/= ( R ` D ) /\ ( R ` x ) =/= ( R ` C ) ) /\ ( ( R ` x ) =/= ( R ` D ) /\ ( R ` x ) =/= ( R ` F ) /\ ( R ` G ) =/= ( R ` x ) ) ) ) -> ( ( D Y G ) ` P ) = ( ( C Y G ) ` P ) )

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
    cD
    cT
    wcel
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
    cC
    cT
    wcel
    #
    vx
    cv
    #
    cT
    wcel
    #
    w3a
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
    w3a
    #
    cG
    @14
    wne
    #
    cC
    @14
    wne
    #
    @7
    @14
    wne
    #
    w3a
    #
    w3a
    #
    cG
    cR
    cfv
    #
    cC
    cR
    cfv
    #
    wne
    #
    @24
    @12
    wne
    #
    cD
    cR
    cfv
    #
    @12
    wne
    #
    w3a
    #
    @23
    @27
    wne
    #
    @7
    cR
    cfv
    #
    @24
    wne
    #
    wa
    #
    @31
    @27
    wne
    #
    @31
    @12
    wne
    #
    @23
    @31
    wne
    #
    w3a
    #
    w3a
    #
    w3a
    #
    cP
    cD
    cG
    cY
    co
    cfv
    #
    cP
    @7
    cG
    cY
    co
    cfv
    #
    cP
    cC
    cG
    cY
    co
    cfv
    #
    @39
    @0
    @1
    @2
    @3
    @5
    @8
    w3a
    #
    @11
    @13
    @15
    @16
    @18
    w3a
    @20
    @36
    @35
    w3a
    #
    @28
    @30
    @34
    w3a
    @40
    @41
    wceq
    @0
    @4
    @9
    @22
    @38
    simp11
    #
    @1
    @2
    @3
    @0
    @9
    @22
    @38
    simp121
    #
    @1
    @2
    @3
    @0
    @9
    @22
    @38
    simp122
    @39
    @3
    @5
    @8
    @1
    @2
    @3
    @0
    @9
    @22
    @38
    simp123
    @5
    @6
    @8
    @0
    @4
    @22
    @38
    simp131
    @5
    @6
    @8
    @0
    @4
    @22
    @38
    simp133
    3jca
    #
    @10
    @11
    @17
    @21
    @38
    simp21
    #
    @13
    @15
    @16
    @11
    @21
    @10
    @38
    simp221
    #
    @39
    @15
    @16
    @18
    @13
    @15
    @16
    @11
    @21
    @10
    @38
    simp222
    #
    @13
    @15
    @16
    @11
    @21
    @10
    @38
    simp223
    @18
    @19
    @20
    @11
    @17
    @10
    @38
    simp231
    #
    3jca
    @39
    @20
    @36
    @35
    @18
    @19
    @20
    @11
    @17
    @10
    @38
    simp233
    @34
    @35
    @36
    @29
    @33
    @10
    @22
    simp333
    @34
    @35
    @36
    @29
    @33
    @10
    @22
    simp332
    3jca
    #
    @39
    @28
    @30
    @34
    @25
    @26
    @28
    @33
    @37
    @10
    @22
    simp313
    @30
    @32
    @29
    @37
    @10
    @22
    simp32l
    @34
    @35
    @36
    @29
    @33
    @10
    @22
    simp331
    3jca
    cA
    cB
    @7
    cD
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
    cdlemk22-3
    syl333anc
    @39
    @0
    @1
    @6
    @43
    @11
    @13
    @15
    @19
    @18
    w3a
    @44
    @26
    @25
    @32
    w3a
    @42
    @41
    wceq
    @45
    @46
    @5
    @6
    @8
    @0
    @4
    @22
    @38
    simp132
    @47
    @48
    @49
    @39
    @15
    @19
    @18
    @50
    @18
    @19
    @20
    @11
    @17
    @10
    @38
    simp232
    @51
    3jca
    @52
    @39
    @26
    @25
    @32
    @25
    @26
    @28
    @33
    @37
    @10
    @22
    simp312
    @25
    @26
    @28
    @33
    @37
    @10
    @22
    simp311
    @30
    @32
    @29
    @37
    @10
    @22
    simp32r
    3jca
    cA
    cB
    @7
    cC
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
    cdlemk22-3
    syl333anc
    eqtr4d
end
