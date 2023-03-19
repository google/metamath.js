include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "wb.mm"
include "ibar.mm"
include "3anass.mm"
include "3ancoma.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "ad2antlr.mm"
include "rabbidva.mm"
include "sylbi.mm"

theorem rusgrnumwwlkslem
  let wph: wff ph
  let wps: wff ps
  let vw: setvar w
  let cP: class P
  let cX: class X
  let cY: class Y
  let cZ: class Z

  disjoint P w
  disjoint Y w
  disjoint Z w
  assert |- ( Y e. { w e. Z | ( w ` 0 ) = P } -> { w e. X | ( ph /\ ps ) } = { w e. X | ( ph /\ ( Y ` 0 ) = P /\ ps ) } )

  proof
    cY
    cc0
    vw
    cv
    #
    cfv
    #
    cP
    wceq
    #
    vw
    cZ
    crab
    wcel
    cY
    cZ
    wcel
    #
    cc0
    cY
    cfv
    #
    cP
    wceq
    #
    wa
    #
    wph
    wps
    wa
    #
    vw
    cX
    crab
    wph
    @5
    wps
    w3a
    #
    vw
    cX
    crab
    wceq
    @2
    @5
    vw
    cY
    cZ
    @0
    cY
    wceq
    @1
    @4
    cP
    cc0
    @0
    cY
    fveq1
    eqeq1d
    elrab
    @6
    @7
    @8
    vw
    cX
    @5
    @7
    @8
    wb
    @3
    @0
    cX
    wcel
    @5
    @7
    @5
    @7
    wa
    #
    @8
    @5
    @7
    ibar
    @9
    @5
    wph
    wps
    w3a
    @8
    @5
    wph
    wps
    3anass
    @5
    wph
    wps
    3ancoma
    bitr3i
    syl6bb
    ad2antlr
    rabbidva
    sylbi
end
