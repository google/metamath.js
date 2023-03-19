include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "ctrl.mm"
include "cfv.mm"
include "cple.mm"
include "eqid.mm"
include "id.mm"
include "cid.mm"
include "cres.mm"
include "cv.mm"
include "idltrn.mm"
include "adantr.mm"
include "tendo0cbv.mm"
include "fmptd.mm"
include "tendo0co2.mm"
include "tendo0tp.mm"
include "istendod.mm"

theorem tendo0cl
  let cB: class B
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  let vg: setvar g
  let vh: setvar h
  assume tendo0.b: |- B = ( Base ` K )
  assume tendo0.h: |- H = ( LHyp ` K )
  assume tendo0.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendo0.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendo0.o: |- O = ( f e. T |-> ( _I |` B ) )

  disjoint B f
  disjoint T f
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
  assert |- ( ( K e. HL /\ W e. H ) -> O e. E )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cO
    cT
    vg
    vh
    cE
    cH
    cK
    cK
    cple
    cfv
    #
    chlt
    cW
    @2
    eqid
    #
    tendo0.h
    tendo0.t
    @1
    eqid
    #
    tendo0.e
    @0
    id
    @0
    vg
    cT
    cid
    cB
    cres
    #
    cT
    cO
    @0
    @5
    cT
    wcel
    vg
    cv
    #
    cT
    wcel
    cB
    cT
    cH
    cK
    cW
    tendo0.b
    tendo0.h
    tendo0.t
    idltrn
    adantr
    cB
    cT
    vf
    vg
    cO
    tendo0.o
    tendo0cbv
    fmptd
    cB
    cT
    vf
    cE
    @6
    vh
    cv
    cH
    cK
    cO
    cW
    tendo0.b
    tendo0.h
    tendo0.t
    tendo0.e
    tendo0.o
    tendo0co2
    cB
    @1
    cT
    vf
    cE
    @6
    cH
    cK
    @2
    cO
    cW
    tendo0.b
    tendo0.h
    tendo0.t
    tendo0.e
    tendo0.o
    @3
    @4
    tendo0tp
    istendod
end
