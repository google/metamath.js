include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cmhm.mm"
include "co.mm"
include "cghm.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "pwsdiagmhm.mm"
include "sylan.mm"
include "wceq.mm"
include "pwsgrp.mm"
include "ghmmhmb.mm"
include "syldan.mm"
include "eleqtrrd.mm"

theorem pwsdiagghm
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cF: class F
  let cI: class I
  let cW: class W
  let cY: class Y
  assume pwsdiagghm.y: |- Y = ( R ^s I )
  assume pwsdiagghm.b: |- B = ( Base ` R )
  assume pwsdiagghm.f: |- F = ( x e. B |-> ( I X. { x } ) )

  disjoint Y x
  disjoint R x
  disjoint I x
  disjoint B x
  disjoint W x
  assert |- ( ( R e. Grp /\ I e. W ) -> F e. ( R GrpHom Y ) )

  proof
    cR
    cgrp
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    cF
    cR
    cY
    cmhm
    co
    #
    cR
    cY
    cghm
    co
    #
    @0
    cR
    cmnd
    wcel
    @1
    cF
    @2
    wcel
    cR
    grpmnd
    vx
    cB
    cR
    cF
    cI
    cW
    cY
    pwsdiagghm.y
    pwsdiagghm.b
    pwsdiagghm.f
    pwsdiagmhm
    sylan
    @0
    @1
    cY
    cgrp
    wcel
    @3
    @2
    wceq
    cR
    cI
    cW
    cY
    pwsdiagghm.y
    pwsgrp
    cR
    cY
    ghmmhmb
    syldan
    eleqtrrd
end
