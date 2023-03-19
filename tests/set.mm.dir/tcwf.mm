include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "ctc.mm"
include "cfv.mm"
include "wss.mm"
include "r1elssi.mm"
include "wtr.mm"
include "cv.mm"
include "dftr3.mm"
include "mprgbir.mm"
include "tcmin.mm"
include "mpan2i.mm"
include "mpd.mm"
include "fvex.mm"
include "r1elss.mm"
include "sylibr.mm"

theorem tcwf
  let cA: class A
  let vx: setvar x


  assert |- ( A e. U. ( R1 " On ) -> ( TC ` A ) e. U. ( R1 " On ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    cA
    ctc
    cfv
    #
    @0
    wss
    #
    @2
    @0
    wcel
    @1
    cA
    @0
    wss
    #
    @3
    cA
    r1elssi
    @1
    @4
    @0
    wtr
    #
    @3
    @5
    vx
    cv
    #
    @0
    wss
    vx
    @0
    vx
    @0
    dftr3
    @6
    r1elssi
    mprgbir
    cA
    @0
    @0
    tcmin
    mpan2i
    mpd
    @2
    cA
    ctc
    fvex
    r1elss
    sylibr
end
