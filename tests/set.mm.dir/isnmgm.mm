include "wcel.mm"
include "co.mm"
include "wnel.mm"
include "cmgm.mm"
include "wa.mm"
include "mgmcl.mm"
include "3expib.mm"
include "com12.mm"
include "nelcon3d.mm"
include "3impia.mm"

theorem isnmgm
  let cB: class B
  let cM: class M
  let cX: class X
  let cY: class Y
  let c.op: class .o.
  let vx: setvar x
  let vy: setvar y
  assume mgmcl.b: |- B = ( Base ` M )
  assume mgmcl.o: |- .o. = ( +g ` M )


  assert |- ( ( X e. B /\ Y e. B /\ ( X .o. Y ) e/ B ) -> M e/ Mgm )

  proof
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cX
    cY
    c.op
    co
    #
    cB
    wnel
    cM
    cmgm
    wnel
    @0
    @1
    wa
    #
    cM
    cmgm
    @2
    cB
    cM
    cmgm
    wcel
    #
    @3
    @2
    cB
    wcel
    #
    @4
    @0
    @1
    @5
    cB
    cM
    cX
    cY
    c.op
    mgmcl.b
    mgmcl.o
    mgmcl
    3expib
    com12
    nelcon3d
    3impia
end
