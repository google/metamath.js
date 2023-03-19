include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wtr.mm"
include "cv.mm"
include "cpw.mm"
include "wcel.mm"
include "cpr.mm"
include "wral.mm"
include "wf.mm"
include "crn.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "cgru.mm"
include "cin.mm"
include "wss.mm"
include "dftr3.mm"
include "r1elssi.mm"
include "mprgbir.mm"
include "pwwf.mm"
include "biimpi.mm"
include "prwf.mm"
include "ralrimiva.mm"
include "frn.mm"
include "vex.mm"
include "rnex.mm"
include "r1elss.mm"
include "uniwf.mm"
include "bitr3i.mm"
include "sylib.mm"
include "ax-gen.mm"
include "a1i.mm"
include "3jca.mm"
include "rgen.mm"
include "ingru.mm"
include "mp2an.mm"

theorem wfgru
  let cU: class U
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( U e. Univ -> ( U i^i U. ( R1 " On ) ) e. Univ )

  proof
    cr1
    con0
    cima
    cuni
    #
    wtr
    #
    vx
    cv
    #
    cpw
    @0
    wcel
    #
    @2
    vy
    cv
    #
    cpr
    @0
    wcel
    #
    vy
    @0
    wral
    #
    @2
    @0
    @4
    wf
    #
    @4
    crn
    #
    cuni
    @0
    wcel
    #
    wi
    #
    vy
    wal
    #
    w3a
    #
    vx
    @0
    wral
    cU
    cgru
    wcel
    cU
    @0
    cin
    cgru
    wcel
    wi
    @1
    @2
    @0
    wss
    vx
    @0
    vx
    @0
    dftr3
    @2
    r1elssi
    mprgbir
    @12
    vx
    @0
    @2
    @0
    wcel
    #
    @3
    @6
    @11
    @13
    @3
    @2
    pwwf
    biimpi
    @13
    @5
    vy
    @0
    @2
    @4
    prwf
    ralrimiva
    @11
    @13
    @10
    vy
    @7
    @8
    @0
    wss
    #
    @9
    @2
    @0
    @4
    frn
    @14
    @8
    @0
    wcel
    @9
    @8
    @4
    vy
    vex
    rnex
    r1elss
    @8
    uniwf
    bitr3i
    sylib
    ax-gen
    a1i
    3jca
    rgen
    vx
    vy
    @0
    cU
    ingru
    mp2an
end
