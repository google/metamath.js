include "wcel.mm"
include "ccom.mm"
include "cvv.mm"
include "co.mm"
include "wceq.mm"
include "coexg.mm"
include "cv.mm"
include "coeq1.mm"
include "coeq2.mm"
include "cmulr.mm"
include "cfv.mm"
include "cmpt2.mm"
include "mendmulrfval.mm"
include "eqtri.mm"
include "ovmpt2g.mm"
include "mpd3an3.mm"

theorem mendmulr
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cM: class M
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume mendmulrfval.a: |- A = ( MEndo ` M )
  assume mendmulrfval.b: |- B = ( Base ` A )
  assume mendmulr.q: |- .x. = ( .r ` A )


  assert |- ( ( X e. B /\ Y e. B ) -> ( X .x. Y ) = ( X o. Y ) )

  proof
    cX
    cB
    wcel
    cY
    cB
    wcel
    cX
    cY
    ccom
    #
    cvv
    wcel
    cX
    cY
    c.x
    co
    @0
    wceq
    cX
    cY
    cB
    cB
    coexg
    vx
    vy
    cX
    cY
    cB
    cB
    vx
    cv
    #
    vy
    cv
    #
    ccom
    #
    @0
    c.x
    cX
    @2
    ccom
    cvv
    @1
    cX
    @2
    coeq1
    @2
    cY
    cX
    coeq2
    c.x
    cA
    cmulr
    cfv
    vx
    vy
    cB
    cB
    @3
    cmpt2
    mendmulr.q
    vx
    vy
    cA
    cB
    cM
    mendmulrfval.a
    mendmulrfval.b
    mendmulrfval
    eqtri
    ovmpt2g
    mpd3an3
end
