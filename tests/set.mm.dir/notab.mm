include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cab.mm"
include "cdif.mm"
include "crab.mm"
include "df-rab.mm"
include "rabab.mm"
include "eqtr3i.mm"
include "difab.mm"
include "abid2.mm"
include "difeq1i.mm"

theorem notab
  let wph: wff ph
  let vx: setvar x


  assert |- { x | -. ph } = ( _V \ { x | ph } )

  proof
    vx
    cv
    cvv
    wcel
    #
    wph
    wn
    #
    wa
    vx
    cab
    #
    @1
    vx
    cab
    #
    cvv
    wph
    vx
    cab
    #
    cdif
    #
    @1
    vx
    cvv
    crab
    @2
    @3
    @1
    vx
    cvv
    df-rab
    @1
    vx
    rabab
    eqtr3i
    @0
    vx
    cab
    #
    @4
    cdif
    @2
    @5
    @0
    wph
    vx
    difab
    @6
    cvv
    @4
    vx
    cvv
    abid2
    difeq1i
    eqtr3i
    eqtr3i
end
