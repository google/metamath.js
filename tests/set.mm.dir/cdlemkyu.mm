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
include "csb.mm"
include "co.mm"
include "cdlemky.mm"
include "simp3l.mm"
include "simp13l.mm"
include "cdlemkuu.mm"
include "syl2anc.mm"
include "fveq1d.mm"
include "eqtrd.mm"

theorem cdlemkyu
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
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
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  let vd: setvar d
  assume cdlemk5.b: |- B = ( Base ` K )
  assume cdlemk5.l: |- .<_ = ( le ` K )
  assume cdlemk5.j: |- .\/ = ( join ` K )
  assume cdlemk5.m: |- ./\ = ( meet ` K )
  assume cdlemk5.a: |- A = ( Atoms ` K )
  assume cdlemk5.h: |- H = ( LHyp ` K )
  assume cdlemk5.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk5.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk5.z: |- Z = ( ( P .\/ ( R ` b ) ) ./\ ( ( N ` P ) .\/ ( R ` ( b o. `' F ) ) ) )
  assume cdlemk5.y: |- Y = ( ( P .\/ ( R ` g ) ) ./\ ( Z .\/ ( R ` ( g o. `' b ) ) ) )
  assume cdlemk5b.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk5b.u1: |- V = ( d e. T , e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( ( S ` d ) ` P ) .\/ ( R ` ( e o. `' d ) ) ) ) ) )
  assume cdlemk5.o2: |- Q = ( S ` b )
  assume cdlemk5.u2: |- C = ( e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( Q ` P ) .\/ ( R ` ( e o. `' b ) ) ) ) ) )

  disjoint d g
  disjoint e g
  disjoint f g
  disjoint g i
  disjoint g j
  disjoint ./\ g
  disjoint d e
  disjoint d f
  disjoint d i
  disjoint d j
  disjoint ./\ d
  disjoint e f
  disjoint e i
  disjoint e j
  disjoint ./\ e
  disjoint f i
  disjoint f j
  disjoint ./\ f
  disjoint i j
  disjoint ./\ i
  disjoint ./\ j
  disjoint .<_ i
  disjoint .<_ j
  disjoint .\/ g
  disjoint .\/ d
  disjoint .\/ e
  disjoint .\/ f
  disjoint .\/ i
  disjoint .\/ j
  disjoint A i
  disjoint A j
  disjoint F f
  disjoint F i
  disjoint F j
  disjoint G g
  disjoint G d
  disjoint G e
  disjoint G j
  disjoint H i
  disjoint H j
  disjoint K i
  disjoint K j
  disjoint N f
  disjoint N i
  disjoint N j
  disjoint P g
  disjoint P d
  disjoint P e
  disjoint P f
  disjoint P i
  disjoint P j
  disjoint R g
  disjoint R d
  disjoint R e
  disjoint R f
  disjoint R i
  disjoint R j
  disjoint b d
  disjoint b e
  disjoint b j
  disjoint S b
  disjoint S d
  disjoint S e
  disjoint S j
  disjoint T g
  disjoint T d
  disjoint T e
  disjoint T f
  disjoint T i
  disjoint T j
  disjoint W d
  disjoint W e
  disjoint W f
  disjoint W i
  disjoint W j
  disjoint Z g
  disjoint b g
  disjoint b f
  disjoint b i
  disjoint Q d
  disjoint Q e
  disjoint ./\ g
  disjoint .\/ g
  disjoint B g
  disjoint P g
  disjoint R g
  disjoint T g
  disjoint Z g
  disjoint b g
  disjoint G g
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( b e. T /\ ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) ) ) -> [_ G / g ]_ Y = ( ( C ` G ) ` P ) )

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
    cF
    cid
    cB
    cres
    #
    wne
    wa
    #
    cG
    cT
    wcel
    #
    cG
    @1
    wne
    #
    wa
    w3a
    #
    cN
    cT
    wcel
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    w3a
    #
    vb
    cv
    #
    cT
    wcel
    #
    @8
    @1
    wne
    @8
    cR
    cfv
    #
    @6
    wne
    @10
    cG
    cR
    cfv
    wne
    w3a
    #
    wa
    #
    w3a
    #
    vg
    cG
    cY
    csb
    cP
    @8
    cG
    cV
    co
    #
    cfv
    cP
    cG
    cC
    cfv
    #
    cfv
    cA
    cB
    cP
    cR
    cS
    cT
    ve
    vf
    vg
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
    cV
    cW
    cY
    cZ
    vb
    vd
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemk5.z
    cdlemk5.y
    cdlemk5b.s
    cdlemk5b.u1
    cdlemky
    @13
    cP
    @14
    @15
    @13
    @9
    @3
    @14
    @15
    wceq
    @5
    @7
    @9
    @11
    simp3l
    @3
    @4
    @0
    @2
    @7
    @12
    simp13l
    cA
    cB
    @8
    cP
    cQ
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
    cV
    cC
    vd
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemk5b.s
    cdlemk5b.u1
    cdlemk5.o2
    cdlemk5.u2
    cdlemkuu
    syl2anc
    fveq1d
    eqtrd
end
