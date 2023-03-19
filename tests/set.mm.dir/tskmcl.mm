include "cvv.mm"
include "wcel.mm"
include "ctskm.mm"
include "cfv.mm"
include "ctsk.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "tskmval.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "wrex.mm"
include "cuni.mm"
include "id.mm"
include "grothtsk.mm"
include "syl6eleqr.mm"
include "eluni2.mm"
include "sylib.mm"
include "rabn0.mm"
include "sylibr.mm"
include "inttsk.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "wn.mm"
include "fvprc.mm"
include "0tsk.mm"
include "syl6eqel.mm"
include "pm2.61i.mm"

theorem tskmcl
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( tarskiMap ` A ) e. Tarski

  proof
    cA
    cvv
    wcel
    #
    cA
    ctskm
    cfv
    #
    ctsk
    wcel
    @0
    @1
    cA
    vx
    cv
    wcel
    #
    vx
    ctsk
    crab
    #
    cint
    #
    ctsk
    vx
    cA
    cvv
    tskmval
    @0
    @3
    ctsk
    wss
    @3
    c0
    wne
    #
    @4
    ctsk
    wcel
    @2
    vx
    ctsk
    ssrab2
    @0
    @2
    vx
    ctsk
    wrex
    #
    @5
    @0
    cA
    ctsk
    cuni
    #
    wcel
    @6
    @0
    cA
    cvv
    @7
    @0
    id
    grothtsk
    syl6eleqr
    vx
    cA
    ctsk
    eluni2
    sylib
    @2
    vx
    ctsk
    rabn0
    sylibr
    @3
    inttsk
    sylancr
    eqeltrd
    @0
    wn
    @1
    c0
    ctsk
    cA
    ctskm
    fvprc
    0tsk
    syl6eqel
    pm2.61i
end
