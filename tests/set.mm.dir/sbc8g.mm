include "cv.mm"
include "wsbc.mm"
include "cab.mm"
include "wcel.mm"
include "dfsbcq.mm"
include "eleq1.mm"
include "wsb.mm"
include "df-clab.mm"
include "weq.mm"
include "wb.mm"
include "equid.mm"
include "dfsbcq2.mm"
include "ax-mp.mm"
include "bitr2i.mm"
include "vtoclbg.mm"

theorem sbc8g
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y


  assert |- ( A e. V -> ( [. A / x ]. ph <-> A e. { x | ph } ) )

  proof
    wph
    vx
    vy
    cv
    #
    wsbc
    #
    @0
    wph
    vx
    cab
    #
    wcel
    #
    wph
    vx
    cA
    wsbc
    cA
    @2
    wcel
    vy
    cA
    cV
    wph
    vx
    @0
    cA
    dfsbcq
    @0
    cA
    @2
    eleq1
    @3
    wph
    vx
    vy
    wsb
    #
    @1
    wph
    vy
    vx
    df-clab
    vy
    vy
    weq
    @4
    @1
    wb
    vy
    equid
    wph
    vx
    vy
    @0
    dfsbcq2
    ax-mp
    bitr2i
    vtoclbg
end
