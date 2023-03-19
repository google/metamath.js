include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "grpinvcl.mm"
include "3adant2.mm"
include "mulginvcom.mm"
include "syld3an3.mm"
include "grpinvinv.mm"
include "oveq2d.mm"
include "eqtr3d.mm"

theorem mulginvinv
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cI: class I
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume mulginvcom.b: |- B = ( Base ` G )
  assume mulginvcom.t: |- .x. = ( .g ` G )
  assume mulginvcom.i: |- I = ( invg ` G )


  assert |- ( ( G e. Grp /\ N e. ZZ /\ X e. B ) -> ( I ` ( N .x. ( I ` X ) ) ) = ( N .x. X ) )

  proof
    cG
    cgrp
    wcel
    #
    cN
    cz
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cN
    cX
    cI
    cfv
    #
    cI
    cfv
    #
    c.x
    co
    #
    cN
    @4
    c.x
    co
    cI
    cfv
    #
    cN
    cX
    c.x
    co
    @0
    @1
    @2
    @4
    cB
    wcel
    #
    @6
    @7
    wceq
    @0
    @2
    @8
    @1
    cB
    cG
    cI
    cX
    mulginvcom.b
    mulginvcom.i
    grpinvcl
    3adant2
    cB
    c.x
    cG
    cI
    cN
    @4
    mulginvcom.b
    mulginvcom.t
    mulginvcom.i
    mulginvcom
    syld3an3
    @3
    @5
    cX
    cN
    c.x
    @0
    @2
    @5
    cX
    wceq
    @1
    cB
    cG
    cI
    cX
    mulginvcom.b
    mulginvcom.i
    grpinvinv
    3adant2
    oveq2d
    eqtr3d
end
