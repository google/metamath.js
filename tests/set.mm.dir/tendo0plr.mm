include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "tendo0cl.mm"
include "adantr.mm"
include "tendoplcom.mm"
include "mpd3an3.mm"
include "tendo0pl.mm"
include "eqtrd.mm"

theorem tendo0plr
  let vt: setvar t
  let cB: class B
  let cP: class P
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  let vs: setvar s
  let vg: setvar g
  let vh: setvar h
  assume tendo0.b: |- B = ( Base ` K )
  assume tendo0.h: |- H = ( LHyp ` K )
  assume tendo0.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendo0.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendo0.o: |- O = ( f e. T |-> ( _I |` B ) )
  assume tendo0pl.p: |- P = ( s e. E , t e. E |-> ( f e. T |-> ( ( s ` f ) o. ( t ` f ) ) ) )

  disjoint B f
  disjoint T f
  disjoint s t
  disjoint E s
  disjoint E t
  disjoint T s
  disjoint T t
  disjoint f s
  disjoint f t
  disjoint W f
  disjoint W s
  disjoint W t
  disjoint B g
  disjoint g h
  disjoint H g
  disjoint H h
  disjoint K g
  disjoint K h
  disjoint O g
  disjoint O h
  disjoint T g
  disjoint T h
  disjoint W g
  disjoint W h
  disjoint g s
  disjoint g t
  disjoint E g
  disjoint P g
  disjoint S g
  assert |- ( ( ( K e. HL /\ W e. H ) /\ S e. E ) -> ( S P O ) = S )

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
    cO
    cP
    co
    #
    cO
    cS
    cP
    co
    #
    cS
    @0
    @1
    cO
    cE
    wcel
    #
    @2
    @3
    wceq
    @0
    @4
    @1
    cB
    cT
    vf
    cE
    cH
    cK
    cO
    cW
    tendo0.b
    tendo0.h
    tendo0.t
    tendo0.e
    tendo0.o
    tendo0cl
    adantr
    vt
    cP
    cT
    cS
    vf
    cE
    cH
    cK
    cO
    cW
    vs
    tendo0.h
    tendo0.t
    tendo0.e
    tendo0pl.p
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
    cK
    cO
    cW
    vs
    tendo0.b
    tendo0.h
    tendo0.t
    tendo0.e
    tendo0.o
    tendo0pl.p
    tendo0pl
    eqtrd
end
