include "cv.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "wceq.mm"
include "crio.mm"
include "cmpt2.mm"
include "eqid.mm"
include "cdlemkyu.mm"

theorem cdlemkyuu
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
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
  assume cdlemk5c.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk5a.u2: |- C = ( e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( ( S ` b ) ` P ) .\/ ( R ` ( e o. `' b ) ) ) ) ) )

  disjoint e g
  disjoint f g
  disjoint g i
  disjoint g j
  disjoint ./\ g
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
  disjoint P e
  disjoint P f
  disjoint P i
  disjoint P j
  disjoint R g
  disjoint R e
  disjoint R f
  disjoint R i
  disjoint R j
  disjoint b e
  disjoint b j
  disjoint S b
  disjoint S e
  disjoint S j
  disjoint T g
  disjoint T e
  disjoint T f
  disjoint T i
  disjoint T j
  disjoint W e
  disjoint W f
  disjoint W i
  disjoint W j
  disjoint Z g
  disjoint b g
  disjoint b f
  disjoint b i
  disjoint ./\ g
  disjoint .\/ g
  disjoint B g
  disjoint P g
  disjoint R g
  disjoint T g
  disjoint Z g
  disjoint b g
  disjoint G g
  disjoint d g
  disjoint d e
  disjoint d f
  disjoint d i
  disjoint d j
  disjoint ./\ d
  disjoint .\/ d
  disjoint G d
  disjoint P d
  disjoint R d
  disjoint b d
  disjoint S d
  disjoint T d
  disjoint W d
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( b e. T /\ ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) ) ) -> [_ G / g ]_ Y = ( ( C ` G ) ` P ) )

  proof
    cA
    cB
    cC
    cP
    vb
    cv
    cS
    cfv
    #
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
    vd
    ve
    cT
    cT
    cP
    vj
    cv
    cfv
    cP
    ve
    cv
    #
    cR
    cfv
    c.or
    co
    cP
    vd
    cv
    #
    cS
    cfv
    cfv
    @1
    @2
    ccnv
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    wceq
    vj
    cT
    crio
    cmpt2
    #
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
    cdlemk5c.s
    @3
    eqid
    @0
    eqid
    cdlemk5a.u2
    cdlemkyu
end
