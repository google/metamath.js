include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cple.mm"
include "wbr.mm"
include "wn.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3.mm"
include "eqid.mm"
include "coc.mm"
include "fveq1i.mm"
include "eqtri.mm"
include "lhpocnel2.mm"
include "3ad2ant1.mm"
include "cdlemk56.mm"
include "syl311anc.mm"
include "cdlemk19w.mm"
include "jca.mm"

theorem cdlemk56w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cN: class N
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  assume cdlemk6.b: |- B = ( Base ` K )
  assume cdlemk6.j: |- .\/ = ( join ` K )
  assume cdlemk6.m: |- ./\ = ( meet ` K )
  assume cdlemk6.o: |- ._|_ = ( oc ` K )
  assume cdlemk6.a: |- A = ( Atoms ` K )
  assume cdlemk6.h: |- H = ( LHyp ` K )
  assume cdlemk6.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk6.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk6.p: |- P = ( ._|_ ` W )
  assume cdlemk6.z: |- Z = ( ( P .\/ ( R ` b ) ) ./\ ( ( N ` P ) .\/ ( R ` ( b o. `' F ) ) ) )
  assume cdlemk6.y: |- Y = ( ( P .\/ ( R ` g ) ) ./\ ( Z .\/ ( R ` ( g o. `' b ) ) ) )
  assume cdlemk6.x: |- X = ( iota_ z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` g ) ) -> ( z ` P ) = Y ) )
  assume cdlemk6.u: |- U = ( g e. T |-> if ( F = N , g , X ) )
  assume cdlemk6.e: |- E = ( ( TEndo ` K ) ` W )

  disjoint b g
  disjoint b z
  disjoint ./\ b
  disjoint g z
  disjoint ./\ g
  disjoint ./\ z
  disjoint .\/ b
  disjoint .\/ g
  disjoint .\/ z
  disjoint A b
  disjoint A g
  disjoint A z
  disjoint B b
  disjoint B g
  disjoint B z
  disjoint F b
  disjoint F g
  disjoint F z
  disjoint H b
  disjoint H g
  disjoint H z
  disjoint K b
  disjoint K g
  disjoint K z
  disjoint N b
  disjoint N g
  disjoint N z
  disjoint P b
  disjoint P g
  disjoint P z
  disjoint R b
  disjoint R g
  disjoint R z
  disjoint T b
  disjoint T g
  disjoint T z
  disjoint W b
  disjoint W g
  disjoint W z
  disjoint Y z
  disjoint Z g
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ N e. T ) /\ ( R ` F ) = ( R ` N ) ) -> ( U e. E /\ ( U ` F ) = N ) )

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
    cN
    cT
    wcel
    #
    wa
    #
    cF
    cR
    cfv
    cN
    cR
    cfv
    wceq
    #
    w3a
    #
    cU
    cE
    wcel
    #
    cF
    cU
    cfv
    cN
    wceq
    @5
    @0
    @1
    @2
    @4
    cP
    cA
    wcel
    cP
    cW
    cK
    cple
    cfv
    #
    wbr
    wn
    wa
    #
    @6
    @0
    @3
    @4
    simp1
    @0
    @1
    @2
    @4
    simp2l
    @0
    @1
    @2
    @4
    simp2r
    @0
    @3
    @4
    simp3
    @0
    @3
    @8
    @4
    cA
    cP
    cH
    cK
    @7
    cW
    @7
    eqid
    #
    cdlemk6.a
    cdlemk6.h
    cP
    cW
    c.pe
    cfv
    cW
    cK
    coc
    cfv
    #
    cfv
    cdlemk6.p
    cW
    c.pe
    @10
    cdlemk6.o
    fveq1i
    eqtri
    lhpocnel2
    3ad2ant1
    vz
    cA
    cB
    cP
    cR
    cT
    cU
    vg
    cE
    cF
    cH
    c.or
    cK
    @7
    c.an
    cN
    cW
    cX
    cY
    cZ
    vb
    cdlemk6.b
    @9
    cdlemk6.j
    cdlemk6.m
    cdlemk6.a
    cdlemk6.h
    cdlemk6.t
    cdlemk6.r
    cdlemk6.z
    cdlemk6.y
    cdlemk6.x
    cdlemk6.u
    cdlemk6.e
    cdlemk56
    syl311anc
    vz
    cA
    cB
    cP
    cR
    cT
    cU
    vg
    cF
    cH
    c.or
    cK
    c.an
    cN
    c.pe
    cW
    cX
    cY
    cZ
    vb
    cdlemk6.b
    cdlemk6.j
    cdlemk6.m
    cdlemk6.o
    cdlemk6.a
    cdlemk6.h
    cdlemk6.t
    cdlemk6.r
    cdlemk6.p
    cdlemk6.z
    cdlemk6.y
    cdlemk6.x
    cdlemk6.u
    cdlemk19w
    jca
end
