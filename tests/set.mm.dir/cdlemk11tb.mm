include "cv.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "wceq.mm"
include "crio.mm"
include "cmpt.mm"
include "eqid.mm"
include "cdlemk11ta.mm"

theorem cdlemk11tb
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  let ve: setvar e
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
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

  disjoint ./\ g
  disjoint .\/ g
  disjoint G g
  disjoint P g
  disjoint R g
  disjoint T g
  disjoint Z g
  disjoint b g
  disjoint I g
  disjoint ./\ b
  disjoint .\/ b
  disjoint F b
  disjoint N b
  disjoint P b
  disjoint R b
  disjoint T b
  disjoint ./\ g
  disjoint .\/ g
  disjoint B g
  disjoint P g
  disjoint R g
  disjoint T g
  disjoint Z g
  disjoint b g
  disjoint G g
  disjoint e g
  disjoint f g
  disjoint g i
  disjoint g j
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
  disjoint .\/ e
  disjoint .\/ f
  disjoint .\/ i
  disjoint .\/ j
  disjoint A i
  disjoint A j
  disjoint F f
  disjoint F i
  disjoint F j
  disjoint G e
  disjoint G j
  disjoint H i
  disjoint H j
  disjoint K i
  disjoint K j
  disjoint N f
  disjoint N i
  disjoint N j
  disjoint P e
  disjoint P f
  disjoint P i
  disjoint P j
  disjoint R e
  disjoint R f
  disjoint R i
  disjoint R j
  disjoint T e
  disjoint T f
  disjoint T i
  disjoint T j
  disjoint W e
  disjoint W f
  disjoint W i
  disjoint W j
  disjoint b e
  disjoint b f
  disjoint b i
  disjoint b j
  disjoint F e
  disjoint I e
  disjoint I j
  disjoint N e
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( b e. T /\ ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) /\ ( I e. T /\ I =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` I ) ) ) ) -> [_ G / g ]_ Y .<_ ( [_ I / g ]_ Y .\/ ( R ` ( I o. `' G ) ) ) )

  proof
    cA
    cB
    ve
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
    vb
    cv
    #
    vf
    cT
    cP
    vi
    cv
    cfv
    cP
    vf
    cv
    #
    cR
    cfv
    c.or
    co
    cP
    cN
    cfv
    @2
    cF
    ccnv
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    wceq
    vi
    cT
    crio
    cmpt
    #
    cfv
    cfv
    @0
    @1
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
    cmpt
    #
    cP
    cR
    @3
    cT
    ve
    vf
    vg
    vi
    vj
    cF
    cG
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cY
    cZ
    vb
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
    @3
    eqid
    @4
    eqid
    cdlemk11ta
end
