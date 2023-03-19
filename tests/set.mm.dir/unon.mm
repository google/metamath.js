include "con0.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "eluni2.mm"
include "onelon.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "csuc.mm"
include "vex.mm"
include "sucid.mm"
include "suceloni.mm"
include "elunii.mm"
include "sylancr.mm"
include "impbii.mm"
include "eqriv.mm"

theorem unon
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- U. On = On

  proof
    vx
    con0
    cuni
    #
    con0
    vx
    cv
    #
    @0
    wcel
    #
    @1
    con0
    wcel
    #
    @2
    @1
    vy
    cv
    #
    wcel
    #
    vy
    con0
    wrex
    @3
    vy
    @1
    con0
    eluni2
    @5
    @3
    vy
    con0
    @4
    @1
    onelon
    rexlimiva
    sylbi
    @3
    @1
    @1
    csuc
    #
    wcel
    @6
    con0
    wcel
    @2
    @1
    vx
    vex
    sucid
    @1
    suceloni
    @1
    @6
    con0
    elunii
    sylancr
    impbii
    eqriv
end
