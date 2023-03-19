include "cv.mm"
include "cof.mm"
include "co.mm"
include "oveq12.mm"
include "cplusg.mm"
include "cfv.mm"
include "cmpt2.mm"
include "mendplusgfval.mm"
include "eqtri.mm"
include "ovex.mm"
include "ovmpt2a.mm"

theorem mendplusg
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.pb: class .+b
  let cM: class M
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume mendplusgfval.a: |- A = ( MEndo ` M )
  assume mendplusgfval.b: |- B = ( Base ` A )
  assume mendplusgfval.p: |- .+ = ( +g ` M )
  assume mendplusg.q: |- .+b = ( +g ` A )


  assert |- ( ( X e. B /\ Y e. B ) -> ( X .+b Y ) = ( X oF .+ Y ) )

  proof
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
    c.pl
    cof
    #
    co
    #
    cX
    cY
    @2
    co
    c.pb
    @0
    cX
    @1
    cY
    @2
    oveq12
    c.pb
    cA
    cplusg
    cfv
    vx
    vy
    cB
    cB
    @3
    cmpt2
    mendplusg.q
    vx
    vy
    cA
    cB
    c.pl
    cM
    mendplusgfval.a
    mendplusgfval.b
    mendplusgfval.p
    mendplusgfval
    eqtri
    cX
    cY
    @2
    ovex
    ovmpt2a
end
