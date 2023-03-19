include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp2.mm"
include "tendocl.mm"
include "syl3anc.mm"
include "tendotr.mm"
include "3com23.mm"
include "catm.mm"
include "coc.mm"
include "eqid.mm"
include "cdlemk56w.mm"
include "syl121anc.mm"

theorem cdleml6
  let vz: setvar z
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vb: setvar b
  assume cdleml6.b: |- B = ( Base ` K )
  assume cdleml6.j: |- .\/ = ( join ` K )
  assume cdleml6.m: |- ./\ = ( meet ` K )
  assume cdleml6.h: |- H = ( LHyp ` K )
  assume cdleml6.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdleml6.r: |- R = ( ( trL ` K ) ` W )
  assume cdleml6.p: |- Q = ( ( oc ` K ) ` W )
  assume cdleml6.z: |- Z = ( ( Q .\/ ( R ` b ) ) ./\ ( ( h ` Q ) .\/ ( R ` ( b o. `' ( s ` h ) ) ) ) )
  assume cdleml6.y: |- Y = ( ( Q .\/ ( R ` g ) ) ./\ ( Z .\/ ( R ` ( g o. `' b ) ) ) )
  assume cdleml6.x: |- X = ( iota_ z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` ( s ` h ) ) /\ ( R ` b ) =/= ( R ` g ) ) -> ( z ` Q ) = Y ) )
  assume cdleml6.u: |- U = ( g e. T |-> if ( ( s ` h ) = h , g , X ) )
  assume cdleml6.e: |- E = ( ( TEndo ` K ) ` W )
  assume cdleml6.o: |- .0. = ( f e. T |-> ( _I |` B ) )

  disjoint b g
  disjoint g z
  disjoint ./\ g
  disjoint b z
  disjoint ./\ b
  disjoint ./\ z
  disjoint .\/ b
  disjoint .\/ g
  disjoint .\/ z
  disjoint B b
  disjoint B f
  disjoint B g
  disjoint B z
  disjoint b f
  disjoint f g
  disjoint f z
  disjoint b h
  disjoint g h
  disjoint h z
  disjoint b s
  disjoint g s
  disjoint s z
  disjoint H b
  disjoint H g
  disjoint H z
  disjoint K b
  disjoint K g
  disjoint K z
  disjoint Q b
  disjoint Q g
  disjoint Q z
  disjoint R b
  disjoint R g
  disjoint R z
  disjoint T b
  disjoint T f
  disjoint T g
  disjoint T z
  disjoint W b
  disjoint W g
  disjoint W z
  disjoint Y z
  disjoint Z g
  assert |- ( ( ( K e. HL /\ W e. H ) /\ h e. T /\ ( s e. E /\ s =/= .0. ) ) -> ( U e. E /\ ( U ` ( s ` h ) ) = h ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    vh
    cv
    #
    cT
    wcel
    #
    vs
    cv
    #
    cE
    wcel
    #
    @3
    c.0
    wne
    #
    wa
    #
    w3a
    #
    @0
    @1
    @3
    cfv
    #
    cT
    wcel
    #
    @2
    @8
    cR
    cfv
    @1
    cR
    cfv
    wceq
    #
    cU
    cE
    wcel
    @8
    cU
    cfv
    @1
    wceq
    wa
    @0
    @2
    @6
    simp1
    #
    @7
    @0
    @4
    @2
    @9
    @11
    @0
    @2
    @4
    @5
    simp3l
    @0
    @2
    @6
    simp2
    #
    @3
    cT
    cE
    @1
    cH
    cK
    chlt
    cW
    cdleml6.h
    cdleml6.t
    cdleml6.e
    tendocl
    syl3anc
    @12
    @0
    @6
    @2
    @10
    cB
    cR
    cT
    @3
    vf
    cE
    @1
    cH
    cK
    c.0
    cW
    cdleml6.b
    cdleml6.h
    cdleml6.t
    cdleml6.r
    cdleml6.e
    cdleml6.o
    tendotr
    3com23
    vz
    cK
    catm
    cfv
    #
    cB
    cQ
    cR
    cT
    cU
    vg
    cE
    @8
    cH
    c.or
    cK
    c.an
    @1
    cK
    coc
    cfv
    #
    cW
    cX
    cY
    cZ
    vb
    cdleml6.b
    cdleml6.j
    cdleml6.m
    @14
    eqid
    @13
    eqid
    cdleml6.h
    cdleml6.t
    cdleml6.r
    cdleml6.p
    cdleml6.z
    cdleml6.y
    cdleml6.x
    cdleml6.u
    cdleml6.e
    cdlemk56w
    syl121anc
end
