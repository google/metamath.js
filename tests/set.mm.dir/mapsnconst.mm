include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "snex.mm"
include "elmap.mm"
include "cop.mm"
include "fsn2.mm"
include "simprbi.mm"
include "xpeq1i.mm"
include "fvex.mm"
include "xpsn.mm"
include "eqtr2i.mm"
include "syl6eq.mm"
include "sylbi.mm"
include "oveq2i.mm"
include "eleq2s.mm"

theorem mapsnconst
  let cB: class B
  let cS: class S
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume mapsncnv.s: |- S = { X }
  assume mapsncnv.b: |- B e. _V
  assume mapsncnv.x: |- X e. _V


  assert |- ( F e. ( B ^m S ) -> F = ( S X. { ( F ` X ) } ) )

  proof
    cF
    cS
    cX
    cF
    cfv
    #
    csn
    #
    cxp
    #
    wceq
    #
    cF
    cB
    cX
    csn
    #
    cmap
    co
    #
    cB
    cS
    cmap
    co
    cF
    @5
    wcel
    @4
    cB
    cF
    wf
    #
    @3
    cB
    @4
    cF
    mapsncnv.b
    cX
    snex
    elmap
    @6
    cF
    cX
    @0
    cop
    csn
    #
    @2
    @6
    @0
    cB
    wcel
    cF
    @7
    wceq
    cX
    cB
    cF
    mapsncnv.x
    fsn2
    simprbi
    @2
    @4
    @1
    cxp
    @7
    cS
    @4
    @1
    mapsncnv.s
    xpeq1i
    cX
    @0
    mapsncnv.x
    cX
    cF
    fvex
    xpsn
    eqtr2i
    syl6eq
    sylbi
    cS
    @4
    cB
    cmap
    mapsncnv.s
    oveq2i
    eleq2s
end
