include "wcel.mm"
include "ccom.mm"
include "cvv.mm"
include "co.mm"
include "wceq.mm"
include "coexg.mm"
include "cv.mm"
include "coeq1.mm"
include "coeq2.mm"
include "symgplusg.mm"
include "ovmpt2g.mm"
include "mpd3an3.mm"

theorem symgov
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  assume symgplusg.1: |- G = ( SymGrp ` A )
  assume symgplusg.2: |- B = ( Base ` G )
  assume symgplusg.3: |- .+ = ( +g ` G )


  assert |- ( ( X e. B /\ Y e. B ) -> ( X .+ Y ) = ( X o. Y ) )

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
    c.pl
    co
    @0
    wceq
    cX
    cY
    cB
    cB
    coexg
    vf
    vg
    cX
    cY
    cB
    cB
    vf
    cv
    #
    vg
    cv
    #
    ccom
    @0
    c.pl
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
    cA
    cB
    c.pl
    vf
    vg
    cG
    symgplusg.1
    symgplusg.2
    symgplusg.3
    symgplusg
    ovmpt2g
    mpd3an3
end
