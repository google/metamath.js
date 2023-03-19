include "cep.mm"
include "wse.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "cab.mm"
include "epel.mm"
include "bicomi.mm"
include "abbi2i.mm"
include "vex.mm"
include "eqeltrri.mm"
include "rabssab.mm"
include "ssexi.mm"
include "rgenw.mm"
include "df-se.mm"
include "mpbir.mm"

theorem epse
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- _E Se A

  proof
    cA
    cep
    wse
    vy
    cv
    #
    vx
    cv
    #
    cep
    wbr
    #
    vy
    cA
    crab
    #
    cvv
    wcel
    #
    vx
    cA
    wral
    @4
    vx
    cA
    @3
    @2
    vy
    cab
    #
    @1
    @5
    cvv
    @2
    vy
    @1
    @2
    @0
    @1
    wcel
    vy
    vx
    epel
    bicomi
    abbi2i
    vx
    vex
    eqeltrri
    @2
    vy
    cA
    rabssab
    ssexi
    rgenw
    vx
    vy
    cA
    cep
    df-se
    mpbir
end
