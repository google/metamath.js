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
include "simpl1.mm"
include "simpl2.mm"
include "simpl31.mm"
include "simpl32.mm"
include "simpr.mm"
include "jca.mm"
include "simpl33.mm"
include "cdlemk24-3.mm"
include "syl113anc.mm"
include "simp11.mm"
include "simp121.mm"
include "simp122.mm"
include "3jca.mm"
include "adantr.mm"
include "simp123.mm"
include "simp131.mm"
include "simp132.mm"
include "simp21.mm"
include "simp221.mm"
include "simp222.mm"
include "simp223.mm"
include "simp231.mm"
include "simp232.mm"
include "simp311.mm"
include "simp312.mm"
include "simp313.mm"
include "cdlemk22-3.mm"
include "pm2.61dane.mm"

theorem cdlemk25-3
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ D e. T /\ N e. T ) /\ ( G e. T /\ C e. T /\ x e. T ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( ( R ` F ) = ( R ` N ) /\ F =/= ( _I |` B ) /\ D =/= ( _I |` B ) ) /\ ( G =/= ( _I |` B ) /\ C =/= ( _I |` B ) /\ x =/= ( _I |` B ) ) ) /\ ( ( ( R ` G ) =/= ( R ` C ) /\ ( R ` C ) =/= ( R ` F ) /\ ( R ` D ) =/= ( R ` F ) ) /\ ( R ` G ) =/= ( R ` D ) /\ ( ( R ` x ) =/= ( R ` D ) /\ ( R ` x ) =/= ( R ` F ) /\ ( R ` G ) =/= ( R ` x ) ) ) ) -> ( ( D Y G ) ` P ) = ( ( C Y G ) ` P ) )

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
    @27
    wne
    @31
    @12
    wne
    @23
    @31
    wne
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
    cP
    cC
    cG
    cY
    co
    cfv
    wceq
    #
    @24
    @27
    @34
    @24
    @27
    wceq
    #
    wa
    #
    @10
    @22
    @29
    @30
    @36
    wa
    @32
    @35
    @10
    @22
    @33
    @36
    simpl1
    @10
    @22
    @33
    @36
    simpl2
    @29
    @30
    @32
    @10
    @22
    @36
    simpl31
    @37
    @30
    @36
    @29
    @30
    @32
    @10
    @22
    @36
    simpl32
    @34
    @36
    simpr
    jca
    @29
    @30
    @32
    @10
    @22
    @36
    simpl33
    vx
    cA
    cB
    cC
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
    cdlemk24-3
    syl113anc
    @34
    @24
    @27
    wne
    #
    wa
    #
    @0
    @1
    @2
    w3a
    #
    @3
    @5
    @6
    w3a
    #
    @11
    @13
    w3a
    #
    @15
    @16
    @18
    w3a
    #
    @19
    @25
    @26
    w3a
    #
    @28
    @30
    @38
    w3a
    @35
    @34
    @40
    @38
    @34
    @0
    @1
    @2
    @0
    @4
    @9
    @22
    @33
    simp11
    @1
    @2
    @3
    @0
    @9
    @22
    @33
    simp121
    @1
    @2
    @3
    @0
    @9
    @22
    @33
    simp122
    3jca
    adantr
    @34
    @42
    @38
    @34
    @41
    @11
    @13
    @34
    @3
    @5
    @6
    @1
    @2
    @3
    @0
    @9
    @22
    @33
    simp123
    @5
    @6
    @8
    @0
    @4
    @22
    @33
    simp131
    @5
    @6
    @8
    @0
    @4
    @22
    @33
    simp132
    3jca
    @10
    @11
    @17
    @21
    @33
    simp21
    @13
    @15
    @16
    @11
    @21
    @10
    @33
    simp221
    3jca
    adantr
    @34
    @43
    @38
    @34
    @15
    @16
    @18
    @13
    @15
    @16
    @11
    @21
    @10
    @33
    simp222
    @13
    @15
    @16
    @11
    @21
    @10
    @33
    simp223
    @18
    @19
    @20
    @11
    @17
    @10
    @33
    simp231
    3jca
    adantr
    @34
    @44
    @38
    @34
    @19
    @25
    @26
    @18
    @19
    @20
    @11
    @17
    @10
    @33
    simp232
    @25
    @26
    @28
    @30
    @32
    @10
    @22
    simp311
    @25
    @26
    @28
    @30
    @32
    @10
    @22
    simp312
    3jca
    adantr
    @39
    @28
    @30
    @38
    @34
    @28
    @38
    @25
    @26
    @28
    @30
    @32
    @10
    @22
    simp313
    adantr
    @29
    @30
    @32
    @10
    @22
    @38
    simpl32
    @34
    @38
    simpr
    3jca
    cA
    cB
    cC
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
    syl113anc
    pm2.61dane
end
