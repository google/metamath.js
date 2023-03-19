include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cple.mm"
include "wbr.mm"
include "wn.mm"
include "3simpb.mm"
include "simp2.mm"
include "eqid.mm"
include "lhpocnel.mm"
include "3ad2ant1.mm"
include "eleq1i.mm"
include "breq1i.mm"
include "notbii.mm"
include "anbi12i.mm"
include "sylibr.mm"
include "cdlemk19u.mm"
include "syl3anc.mm"

theorem cdlemk19w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
  let vg: setvar g
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ N e. T ) /\ ( R ` F ) = ( R ` N ) ) -> ( U ` F ) = N )

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
    cN
    cT
    wcel
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
    @0
    @2
    wa
    @1
    cP
    cA
    wcel
    #
    cP
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    wn
    #
    wa
    #
    cF
    cU
    cfv
    cN
    wceq
    @0
    @1
    @2
    3simpb
    @0
    @1
    @2
    simp2
    @3
    cW
    c.pe
    cfv
    #
    cA
    wcel
    #
    @9
    cW
    @5
    wbr
    #
    wn
    #
    wa
    #
    @8
    @0
    @1
    @13
    @2
    cA
    cH
    cK
    @5
    c.pe
    cW
    @5
    eqid
    #
    cdlemk6.o
    cdlemk6.a
    cdlemk6.h
    lhpocnel
    3ad2ant1
    @4
    @10
    @7
    @12
    cP
    @9
    cA
    cdlemk6.p
    eleq1i
    @6
    @11
    cP
    @9
    cW
    @5
    cdlemk6.p
    breq1i
    notbii
    anbi12i
    sylibr
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
    @5
    c.an
    cN
    cW
    cX
    cY
    cZ
    vb
    cdlemk6.b
    @14
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
    cdlemk19u
    syl3anc
end
