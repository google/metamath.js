include "wcel.mm"
include "cv.mm"
include "ctsk.mm"
include "crab.mm"
include "cint.mm"
include "ctskm.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "id.mm"
include "rgenw.mm"
include "elintrabg.mm"
include "mpbiri.mm"
include "tskmval.mm"
include "eleqtrrd.mm"

theorem tskmid
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> A e. ( tarskiMap ` A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cA
    vx
    cv
    wcel
    #
    vx
    ctsk
    crab
    cint
    #
    cA
    ctskm
    cfv
    @0
    cA
    @2
    wcel
    @1
    @1
    wi
    #
    vx
    ctsk
    wral
    @3
    vx
    ctsk
    @1
    id
    rgenw
    @1
    vx
    cA
    ctsk
    cV
    elintrabg
    mpbiri
    vx
    cA
    cV
    tskmval
    eleqtrrd
end
