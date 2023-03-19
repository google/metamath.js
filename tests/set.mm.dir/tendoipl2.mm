include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "tendoicl.mm"
include "tendoplcom.mm"
include "mpd3an3.mm"
include "tendoipl.mm"
include "eqtrd.mm"

theorem tendoipl2
  let vt: setvar t
  let cB: class B
  let cP: class P
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cI: class I
  let cK: class K
  let cO: class O
  let cW: class W
  let vs: setvar s
  let vg: setvar g
  let vh: setvar h
  assume tendoicl.h: |- H = ( LHyp ` K )
  assume tendoicl.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendoicl.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendoicl.i: |- I = ( s e. E |-> ( f e. T |-> `' ( s ` f ) ) )
  assume tendoi.b: |- B = ( Base ` K )
  assume tendoi.p: |- P = ( s e. E , t e. E |-> ( f e. T |-> ( ( s ` f ) o. ( t ` f ) ) ) )
  assume tendoi.o: |- O = ( f e. T |-> ( _I |` B ) )

  disjoint E s
  disjoint f s
  disjoint T f
  disjoint T s
  disjoint W f
  disjoint W s
  disjoint B f
  disjoint E t
  disjoint H f
  disjoint K f
  disjoint f t
  disjoint s t
  disjoint T t
  disjoint W t
  disjoint g h
  disjoint g s
  disjoint E g
  disjoint h s
  disjoint E h
  disjoint H g
  disjoint H h
  disjoint I g
  disjoint I h
  disjoint K g
  disjoint K h
  disjoint S g
  disjoint S h
  disjoint f g
  disjoint f h
  disjoint T g
  disjoint T h
  disjoint W g
  disjoint W h
  disjoint O g
  disjoint P g
  assert |- ( ( ( K e. HL /\ W e. H ) /\ S e. E ) -> ( S P ( I ` S ) ) = O )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cS
    cE
    wcel
    #
    wa
    cS
    cS
    cI
    cfv
    #
    cP
    co
    #
    @2
    cS
    cP
    co
    #
    cO
    @0
    @1
    @2
    cE
    wcel
    @3
    @4
    wceq
    cS
    cT
    vf
    cE
    cH
    cI
    cK
    cW
    vs
    tendoicl.h
    tendoicl.t
    tendoicl.e
    tendoicl.i
    tendoicl
    vt
    cP
    cT
    cS
    vf
    cE
    cH
    cK
    @2
    cW
    vs
    tendoicl.h
    tendoicl.t
    tendoicl.e
    tendoi.p
    tendoplcom
    mpd3an3
    vt
    cB
    cP
    cS
    cT
    vf
    cE
    cH
    cI
    cK
    cO
    cW
    vs
    tendoicl.h
    tendoicl.t
    tendoicl.e
    tendoicl.i
    tendoi.b
    tendoi.p
    tendoi.o
    tendoipl
    eqtrd
end
