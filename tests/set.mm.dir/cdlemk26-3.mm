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
include "cv.mm"
include "wrex.mm"
include "co.mm"
include "simp11l.mm"
include "simp11r.mm"
include "cdlemftr3.mm"
include "syl2anc.mm"
include "simp111.mm"
include "simp112.mm"
include "simp13l.mm"
include "3ad2ant1.mm"
include "simp13r.mm"
include "simp2.mm"
include "3jca.mm"
include "simp121.mm"
include "simp122.mm"
include "simp23l.mm"
include "simp23r.mm"
include "simp3l.mm"
include "simp3r3.mm"
include "simp3r1.mm"
include "simp3r2.mm"
include "necomd.mm"
include "cdlemk25-3.mm"
include "syl333anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem cdlemk26-3
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ D e. T /\ N e. T ) /\ ( G e. T /\ C e. T ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( ( R ` F ) = ( R ` N ) /\ F =/= ( _I |` B ) /\ D =/= ( _I |` B ) ) /\ ( G =/= ( _I |` B ) /\ C =/= ( _I |` B ) ) ) /\ ( ( ( R ` G ) =/= ( R ` C ) /\ ( R ` C ) =/= ( R ` F ) /\ ( R ` D ) =/= ( R ` F ) ) /\ ( R ` G ) =/= ( R ` D ) ) ) -> ( ( D Y G ) ` P ) = ( ( C Y G ) ` P ) )

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
    cD
    cT
    wcel
    cN
    cT
    wcel
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
    cF
    cid
    cB
    cres
    #
    wne
    cD
    @10
    wne
    w3a
    #
    cG
    @10
    wne
    #
    cC
    @10
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
    @17
    @9
    wne
    cD
    cR
    cfv
    #
    @9
    wne
    w3a
    #
    @16
    @18
    wne
    #
    wa
    #
    w3a
    #
    vx
    cv
    #
    @10
    wne
    #
    @23
    cR
    cfv
    #
    @9
    wne
    #
    @25
    @16
    wne
    #
    @25
    @18
    wne
    #
    w3a
    #
    wa
    #
    vx
    cT
    wrex
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
    @22
    @0
    @1
    @31
    @0
    @1
    @3
    @6
    @15
    @21
    simp11l
    @0
    @1
    @3
    @6
    @15
    @21
    simp11r
    cB
    cR
    cT
    vx
    cH
    cK
    cW
    @9
    @16
    @18
    cdlemk3.b
    cdlemk3.h
    cdlemk3.t
    cdlemk3.r
    cdlemftr3
    syl2anc
    @22
    @30
    @32
    vx
    cT
    @22
    @23
    cT
    wcel
    #
    @30
    w3a
    #
    @2
    @3
    @4
    @5
    @33
    w3a
    @8
    @11
    @12
    @13
    @24
    w3a
    @19
    @20
    @28
    @26
    @16
    @25
    wne
    #
    w3a
    @32
    @2
    @3
    @6
    @15
    @21
    @33
    @30
    simp111
    @2
    @3
    @6
    @15
    @21
    @33
    @30
    simp112
    @34
    @4
    @5
    @33
    @22
    @33
    @4
    @30
    @4
    @5
    @2
    @3
    @15
    @21
    simp13l
    3ad2ant1
    @22
    @33
    @5
    @30
    @4
    @5
    @2
    @3
    @15
    @21
    simp13r
    3ad2ant1
    @22
    @33
    @30
    simp2
    3jca
    @8
    @11
    @14
    @7
    @21
    @33
    @30
    simp121
    @8
    @11
    @14
    @7
    @21
    @33
    @30
    simp122
    @34
    @12
    @13
    @24
    @22
    @33
    @12
    @30
    @12
    @13
    @8
    @11
    @7
    @21
    simp23l
    3ad2ant1
    @22
    @33
    @13
    @30
    @12
    @13
    @8
    @11
    @7
    @21
    simp23r
    3ad2ant1
    @22
    @33
    @24
    @29
    simp3l
    3jca
    @19
    @20
    @7
    @15
    @33
    @30
    simp13l
    @19
    @20
    @7
    @15
    @33
    @30
    simp13r
    @34
    @28
    @26
    @35
    @26
    @27
    @28
    @24
    @22
    @33
    simp3r3
    @26
    @27
    @28
    @24
    @22
    @33
    simp3r1
    @34
    @25
    @16
    @26
    @27
    @28
    @24
    @22
    @33
    simp3r2
    necomd
    3jca
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
    cdlemk25-3
    syl333anc
    rexlimdv3a
    mpd
end
