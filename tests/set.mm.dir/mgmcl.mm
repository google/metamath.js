include "cmgm.mm"
include "wcel.mm"
include "co.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "ismgm.mm"
include "ibi.mm"
include "ovrspc2v.mm"
include "expcom.mm"
include "syl.mm"
include "3impib.mm"

theorem mgmcl
  let cB: class B
  let cM: class M
  let cX: class X
  let cY: class Y
  let c.op: class .o.
  let vx: setvar x
  let vy: setvar y
  assume mgmcl.b: |- B = ( Base ` M )
  assume mgmcl.o: |- .o. = ( +g ` M )


  assert |- ( ( M e. Mgm /\ X e. B /\ Y e. B ) -> ( X .o. Y ) e. B )

  proof
    cM
    cmgm
    wcel
    #
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
    cB
    wcel
    #
    @0
    vx
    cv
    vy
    cv
    c.op
    co
    cB
    wcel
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @1
    @2
    wa
    #
    @3
    wi
    @0
    @4
    vx
    vy
    cB
    cM
    cmgm
    c.op
    mgmcl.b
    mgmcl.o
    ismgm
    ibi
    @5
    @4
    @3
    vx
    vy
    cB
    cB
    cB
    c.op
    cX
    cY
    ovrspc2v
    expcom
    syl
    3impib
end
