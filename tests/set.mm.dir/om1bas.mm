include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "crab.mm"
include "cop.mm"
include "cplusg.mm"
include "cpco.mm"
include "cts.mm"
include "cxko.mm"
include "ctp.mm"
include "eqidd.mm"
include "om1val.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "cvv.mm"
include "wcel.mm"
include "ovex.mm"
include "rabex.mm"
include "eqid.mm"
include "topgrpbas.mm"
include "ax-mp.mm"
include "syl6eqr.mm"

theorem om1bas
  let wph: wff ph
  let cB: class B
  let vf: setvar f
  let cJ: class J
  let cO: class O
  let cX: class X
  let cY: class Y
  let cF: class F
  assume om1bas.o: |- O = ( J Om1 Y )
  assume om1bas.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume om1bas.y: |- ( ph -> Y e. X )
  assume om1bas.b: |- ( ph -> B = ( Base ` O ) )

  disjoint J f
  disjoint f ph
  disjoint X f
  disjoint Y f
  disjoint F f
  assert |- ( ph -> B = { f e. ( II Cn J ) | ( ( f ` 0 ) = Y /\ ( f ` 1 ) = Y ) } )

  proof
    wph
    cB
    cnx
    cbs
    cfv
    cc0
    vf
    cv
    #
    cfv
    cY
    wceq
    c1
    @0
    cfv
    cY
    wceq
    wa
    #
    vf
    cii
    cJ
    ccn
    co
    #
    crab
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
    cbs
    cfv
    #
    @3
    wph
    cB
    cO
    cbs
    cfv
    @7
    om1bas.b
    wph
    cO
    @6
    cbs
    wph
    @3
    @4
    vf
    cJ
    @5
    cO
    cX
    cY
    om1bas.o
    wph
    @3
    eqidd
    wph
    @4
    eqidd
    wph
    @5
    eqidd
    om1bas.j
    om1bas.y
    om1val
    fveq2d
    eqtrd
    @3
    cvv
    wcel
    @3
    @7
    wceq
    @1
    vf
    @2
    cii
    cJ
    ccn
    ovex
    rabex
    @3
    @4
    @5
    @6
    cvv
    @6
    eqid
    topgrpbas
    ax-mp
    syl6eqr
end
