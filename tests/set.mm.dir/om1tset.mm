include "cts.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cpco.mm"
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
include "ovex.mm"
include "eqid.mm"
include "topgrptset.mm"
include "ax-mp.mm"
include "syl6reqr.mm"

theorem om1tset
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


  assert |- ( ph -> ( J ^ko II ) = ( TopSet ` O ) )

  proof
    wph
    cO
    cts
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
    cts
    cfv
    #
    @2
    wph
    cO
    @3
    cts
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
    @2
    cvv
    wcel
    @2
    @4
    wceq
    cJ
    cii
    cxko
    ovex
    @0
    @1
    @2
    @3
    cvv
    @3
    eqid
    topgrptset
    ax-mp
    syl6reqr
end
