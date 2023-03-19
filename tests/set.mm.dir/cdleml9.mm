include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "w3a.mm"
include "tendo1ne0.mm"
include "3ad2ant1.mm"
include "wceq.mm"
include "ccom.mm"
include "cdleml8.mm"
include "adantr.mm"
include "coeq1.mm"
include "simp1.mm"
include "simp3l.mm"
include "tendo0mul.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "eqtr3d.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem cdleml9
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( h e. T /\ h =/= ( _I |` B ) ) /\ ( s e. E /\ s =/= .0. ) ) -> U =/= .0. )

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
    @1
    cid
    cB
    cres
    wne
    wa
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
    cid
    cT
    cres
    #
    c.0
    wne
    #
    cU
    c.0
    wne
    @0
    @2
    @9
    @6
    cB
    cT
    vf
    cE
    cH
    cK
    c.0
    cW
    cdleml6.b
    cdleml6.h
    cdleml6.t
    cdleml6.e
    cdleml6.o
    tendo1ne0
    3ad2ant1
    @7
    cU
    c.0
    @8
    c.0
    @7
    cU
    c.0
    wceq
    #
    @8
    c.0
    wceq
    @7
    @10
    wa
    cU
    @3
    ccom
    #
    @8
    c.0
    @7
    @11
    @8
    wceq
    @10
    vz
    cB
    cQ
    cR
    cT
    cU
    vf
    vg
    vh
    cE
    cH
    c.or
    cK
    c.an
    cW
    cX
    cY
    c.0
    cZ
    vs
    vb
    cdleml6.b
    cdleml6.j
    cdleml6.m
    cdleml6.h
    cdleml6.t
    cdleml6.r
    cdleml6.p
    cdleml6.z
    cdleml6.y
    cdleml6.x
    cdleml6.u
    cdleml6.e
    cdleml6.o
    cdleml8
    adantr
    @10
    @7
    @11
    c.0
    @3
    ccom
    #
    c.0
    cU
    c.0
    @3
    coeq1
    @7
    @0
    @4
    @12
    c.0
    wceq
    @0
    @2
    @6
    simp1
    @0
    @2
    @4
    @5
    simp3l
    cB
    cT
    @3
    vf
    cE
    cH
    cK
    c.0
    cW
    cdleml6.b
    cdleml6.h
    cdleml6.t
    cdleml6.e
    cdleml6.o
    tendo0mul
    syl2anc
    sylan9eqr
    eqtr3d
    ex
    necon3d
    mpd
end
