include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "dihf11lem.mm"
include "w3a.mm"
include "dih11.mm"
include "biimpd.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem dihf11
  let cB: class B
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vq: setvar q
  let vu: setvar u
  assume dihf11.b: |- B = ( Base ` K )
  assume dihf11.h: |- H = ( LHyp ` K )
  assume dihf11.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihf11.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihf11.s: |- S = ( LSubSp ` U )


  assert |- ( ( K e. HL /\ W e. H ) -> I : B -1-1-> S )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cB
    cS
    cI
    wf
    vx
    cv
    #
    cI
    cfv
    vy
    cv
    #
    cI
    cfv
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    cB
    cS
    cI
    wf1
    cB
    cS
    cU
    cH
    cI
    cK
    cW
    dihf11.b
    dihf11.h
    dihf11.i
    dihf11.u
    dihf11.s
    dihf11lem
    @0
    @5
    vx
    vy
    cB
    cB
    @0
    @1
    cB
    wcel
    #
    @2
    cB
    wcel
    #
    @5
    @0
    @6
    @7
    w3a
    @3
    @4
    cB
    cH
    cI
    cK
    cW
    @1
    @2
    dihf11.b
    dihf11.h
    dihf11.i
    dih11
    biimpd
    3expb
    ralrimivva
    vx
    vy
    cB
    cS
    cI
    dff13
    sylanbrc
end
