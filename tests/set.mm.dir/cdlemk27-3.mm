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
include "simp11.mm"
include "simp221.mm"
include "simp13l.mm"
include "simp12.mm"
include "simp3l3.mm"
include "simp3r.mm"
include "necomd.mm"
include "jca.mm"
include "simp222.mm"
include "simp23l.mm"
include "simp223.mm"
include "3jca.mm"
include "simp21.mm"
include "cdlemkuel-3.mm"
include "syl313anc.mm"
include "simp121.mm"
include "simp13r.mm"
include "simp123.mm"
include "simp3l2.mm"
include "simp3l1.mm"
include "simp23r.mm"
include "syl333anc.mm"
include "cdlemk26-3.mm"
include "cdlemd.mm"
include "syl311anc.mm"

theorem cdlemk27-3
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
  let vx: setvar x
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
  disjoint Q d
  disjoint Q e
  disjoint b f
  disjoint b i
  disjoint b d
  disjoint b e
  disjoint b j
  disjoint S b
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ D e. T /\ N e. T ) /\ ( G e. T /\ C e. T ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( ( R ` F ) = ( R ` N ) /\ F =/= ( _I |` B ) /\ D =/= ( _I |` B ) ) /\ ( G =/= ( _I |` B ) /\ C =/= ( _I |` B ) ) ) /\ ( ( ( R ` G ) =/= ( R ` C ) /\ ( R ` C ) =/= ( R ` F ) /\ ( R ` D ) =/= ( R ` F ) ) /\ ( R ` G ) =/= ( R ` D ) ) ) -> ( D Y G ) = ( C Y G ) )

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
    wa
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
    @12
    wne
    #
    w3a
    #
    cG
    @12
    wne
    #
    cC
    @12
    wne
    #
    wa
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
    @21
    @10
    wne
    #
    cD
    cR
    cfv
    #
    @10
    wne
    #
    w3a
    #
    @20
    @24
    wne
    #
    wa
    #
    w3a
    #
    @0
    cD
    cG
    cY
    co
    #
    cT
    wcel
    #
    cC
    cG
    cY
    co
    #
    cT
    wcel
    #
    @9
    cP
    @30
    cfv
    cP
    @32
    cfv
    wceq
    @30
    @32
    wceq
    @0
    @4
    @7
    @19
    @28
    simp11
    #
    @29
    @0
    @11
    @5
    @4
    @25
    @24
    @20
    wne
    #
    wa
    @13
    @16
    @14
    w3a
    @9
    @31
    @34
    @11
    @13
    @14
    @9
    @18
    @8
    @28
    simp221
    #
    @5
    @6
    @0
    @4
    @19
    @28
    simp13l
    #
    @0
    @4
    @7
    @19
    @28
    simp12
    @29
    @25
    @35
    @22
    @23
    @25
    @27
    @8
    @19
    simp3l3
    @29
    @20
    @24
    @8
    @19
    @26
    @27
    simp3r
    necomd
    jca
    @29
    @13
    @16
    @14
    @11
    @13
    @14
    @9
    @18
    @8
    @28
    simp222
    #
    @16
    @17
    @9
    @15
    @8
    @28
    simp23l
    #
    @11
    @13
    @14
    @9
    @18
    @8
    @28
    simp223
    3jca
    @8
    @9
    @15
    @18
    @28
    simp21
    #
    cA
    cB
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
    cdlemkuel-3
    syl313anc
    @29
    @0
    @11
    @5
    @1
    @6
    @3
    @23
    @21
    @20
    wne
    #
    wa
    @13
    @16
    @17
    w3a
    @9
    @33
    @34
    @36
    @37
    @1
    @2
    @3
    @0
    @7
    @19
    @28
    simp121
    @5
    @6
    @0
    @4
    @19
    @28
    simp13r
    @1
    @2
    @3
    @0
    @7
    @19
    @28
    simp123
    @29
    @23
    @41
    @22
    @23
    @25
    @27
    @8
    @19
    simp3l2
    @29
    @20
    @21
    @22
    @23
    @25
    @27
    @8
    @19
    simp3l1
    necomd
    jca
    @29
    @13
    @16
    @17
    @38
    @39
    @16
    @17
    @9
    @15
    @8
    @28
    simp23r
    3jca
    @40
    cA
    cB
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
    cdlemkuel-3
    syl333anc
    @40
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
    cdlemk26-3
    cA
    cP
    cT
    @30
    @32
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
end
