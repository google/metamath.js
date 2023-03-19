include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "crab.mm"
include "w3a.mm"
include "om1bas.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "3anass.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem om1elbas
  let wph: wff ph
  let cB: class B
  let cF: class F
  let cJ: class J
  let cO: class O
  let cX: class X
  let cY: class Y
  let vf: setvar f
  assume om1bas.o: |- O = ( J Om1 Y )
  assume om1bas.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume om1bas.y: |- ( ph -> Y e. X )
  assume om1bas.b: |- ( ph -> B = ( Base ` O ) )


  assert |- ( ph -> ( F e. B <-> ( F e. ( II Cn J ) /\ ( F ` 0 ) = Y /\ ( F ` 1 ) = Y ) ) )

  proof
    wph
    cF
    cB
    wcel
    cF
    cc0
    vf
    cv
    #
    cfv
    #
    cY
    wceq
    #
    c1
    @0
    cfv
    #
    cY
    wceq
    #
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
    wcel
    #
    cF
    @6
    wcel
    #
    cc0
    cF
    cfv
    #
    cY
    wceq
    #
    c1
    cF
    cfv
    #
    cY
    wceq
    #
    w3a
    #
    wph
    cB
    @7
    cF
    wph
    cB
    vf
    cJ
    cO
    cX
    cY
    om1bas.o
    om1bas.j
    om1bas.y
    om1bas.b
    om1bas
    eleq2d
    @8
    @9
    @11
    @13
    wa
    #
    wa
    @14
    @5
    @15
    vf
    cF
    @6
    @0
    cF
    wceq
    #
    @2
    @11
    @4
    @13
    @16
    @1
    @10
    cY
    cc0
    @0
    cF
    fveq1
    eqeq1d
    @16
    @3
    @12
    cY
    c1
    @0
    cF
    fveq1
    eqeq1d
    anbi12d
    elrab
    @9
    @11
    @13
    3anass
    bitr4i
    syl6bb
end
