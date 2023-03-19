include "cv.mm"
include "c0.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "weq.mm"
include "wn.mm"
include "crab.mm"
include "equid.mm"
include "noel.mm"
include "intnanr.mm"
include "2th.mm"
include "con2bii.mm"
include "abbii.mm"
include "df-rab.mm"
include "dfnul2.mm"
include "3eqtr4i.mm"

theorem rab0OLD
  let wph: wff ph
  let vx: setvar x


  assert |- { x e. (/) | ph } = (/)

  proof
    vx
    cv
    #
    c0
    wcel
    #
    wph
    wa
    #
    vx
    cab
    vx
    vx
    weq
    #
    wn
    #
    vx
    cab
    wph
    vx
    c0
    crab
    c0
    @2
    @4
    vx
    @3
    @2
    @3
    @2
    wn
    vx
    equid
    @1
    wph
    @0
    noel
    intnanr
    2th
    con2bii
    abbii
    wph
    vx
    c0
    df-rab
    vx
    dfnul2
    3eqtr4i
end
