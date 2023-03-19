include "cplusg.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cpco.mm"
include "cts.mm"
include "cii.mm"
include "cxko.mm"
include "co.mm"
include "ctp.mm"
include "eqidd.mm"
include "om1bas.mm"
include "om1val.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqid.mm"
include "topgrpplusg.mm"
include "ax-mp.mm"
include "syl6reqr.mm"

theorem om1plusg
  let wph: wff ph
  let cJ: class J
  let cO: class O
  let cX: class X
  let cY: class Y
  let cF: class F
  let vf: setvar f
  assume om1bas.o: |- O = ( J Om1 Y )
  assume om1bas.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume om1bas.y: |- ( ph -> Y e. X )


  assert |- ( ph -> ( *p ` J ) = ( +g ` O ) )

  proof
    wph
    cO
    cplusg
    cfv
    cnx
    cbs
    cfv
    cO
    cbs
    cfv
    #
    cop
    cnx
    cplusg
    cfv
    cJ
    cpco
    cfv
    #
    cop
    cnx
    cts
    cfv
    cJ
    cii
    cxko
    co
    #
    cop
    ctp
    #
    cplusg
    cfv
    #
    @1
    wph
    cO
    @3
    cplusg
    wph
    @0
    @1
    vf
    cJ
    @2
    cO
    cX
    cY
    om1bas.o
    wph
    @0
    vf
    cJ
    cO
    cX
    cY
    om1bas.o
    om1bas.j
    om1bas.y
    wph
    @0
    eqidd
    om1bas
    wph
    @1
    eqidd
    wph
    @2
    eqidd
    om1bas.j
    om1bas.y
    om1val
    fveq2d
    @1
    cvv
    wcel
    @1
    @4
    wceq
    cJ
    cpco
    fvex
    @0
    @1
    @2
    @3
    cvv
    @3
    eqid
    topgrpplusg
    ax-mp
    syl6reqr
end
