include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wrex.mm"
include "co.mm"
include "simpl1.mm"
include "cdlemftr2.mm"
include "syl.mm"
include "simp3r.mm"
include "simp11.mm"
include "simp133.mm"
include "simp131.mm"
include "simp121.mm"
include "simp3l.mm"
include "simp123.mm"
include "simp3r2.mm"
include "simp3r3.mm"
include "jca.mm"
include "simp122.mm"
include "simp132.mm"
include "simp3r1.mm"
include "3jca.mm"
include "simp2.mm"
include "cdlemkuel-3.mm"
include "syl333anc.mm"
include "3expia.mm"
include "expd.mm"
include "reximdvai.mm"
include "mpd.mm"

theorem cdlemk26b-3
  let vx: setvar x
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
  let vd: setvar d
  let cD: class D
  let cQ: class Q
  let vb: setvar b
  let cC: class C
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
  disjoint G f
  disjoint G i
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint i x
  disjoint j x
  disjoint .<_ x
  disjoint A x
  disjoint B x
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
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint Q d
  disjoint Q e
  disjoint b f
  disjoint b i
  disjoint b d
  disjoint b e
  disjoint b j
  disjoint S b
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C i
  disjoint C j
  disjoint D x
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) /\ N e. T ) /\ ( G e. T /\ G =/= ( _I |` B ) /\ ( R ` F ) = ( R ` N ) ) ) /\ ( P e. A /\ -. P .<_ W ) ) -> E. x e. T ( ( x =/= ( _I |` B ) /\ ( R ` x ) =/= ( R ` F ) /\ ( R ` x ) =/= ( R ` G ) ) /\ ( x Y G ) e. T ) )

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
    @2
    wne
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
    wa
    #
    vx
    cv
    #
    @2
    wne
    #
    @14
    cR
    cfv
    #
    @8
    wne
    #
    @16
    cG
    cR
    cfv
    #
    wne
    #
    w3a
    #
    vx
    cT
    wrex
    #
    @20
    @14
    cG
    cY
    co
    cT
    wcel
    #
    wa
    #
    vx
    cT
    wrex
    @13
    @0
    @21
    @0
    @5
    @10
    @12
    simpl1
    cB
    cR
    cT
    vx
    cH
    cK
    cW
    @8
    @18
    cdlemk3.b
    cdlemk3.h
    cdlemk3.t
    cdlemk3.r
    cdlemftr2
    syl
    @13
    @20
    @23
    vx
    cT
    @13
    @14
    cT
    wcel
    #
    @20
    @23
    @11
    @12
    @24
    @20
    wa
    #
    @23
    @11
    @12
    @25
    w3a
    #
    @20
    @22
    @11
    @12
    @24
    @20
    simp3r
    @26
    @0
    @9
    @6
    @1
    @24
    @4
    @17
    @19
    wa
    @3
    @7
    @15
    w3a
    @12
    @22
    @0
    @5
    @10
    @12
    @25
    simp11
    @6
    @7
    @9
    @0
    @5
    @12
    @25
    simp133
    @6
    @7
    @9
    @0
    @5
    @12
    @25
    simp131
    @1
    @3
    @4
    @0
    @10
    @12
    @25
    simp121
    @11
    @12
    @24
    @20
    simp3l
    @1
    @3
    @4
    @0
    @10
    @12
    @25
    simp123
    @26
    @17
    @19
    @15
    @17
    @19
    @24
    @11
    @12
    simp3r2
    @15
    @17
    @19
    @24
    @11
    @12
    simp3r3
    jca
    @26
    @3
    @7
    @15
    @1
    @3
    @4
    @0
    @10
    @12
    @25
    simp122
    @6
    @7
    @9
    @0
    @5
    @12
    @25
    simp132
    @15
    @17
    @19
    @24
    @11
    @12
    simp3r1
    3jca
    @11
    @12
    @25
    simp2
    cA
    cB
    @14
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
    jca
    3expia
    expd
    reximdvai
    mpd
end
