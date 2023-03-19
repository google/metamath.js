include "cv.mm"
include "wcel.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cuni.mm"
include "wi.mm"
include "cpw.mm"
include "w3a.mm"
include "crab.mm"
include "wss.mm"
include "wa.mm"
include "cab.mm"
include "cvv.mm"
include "df-rab.mm"
include "selpw.mm"
include "anbi1i.mm"
include "abbii.mm"
include "eqtri.mm"
include "vex.mm"
include "pwexg.mm"
include "mp2b.mm"
include "rabex.mm"
include "eqeltrri.mm"

theorem sigaex
  let vx: setvar x
  let vo: setvar o
  let vs: setvar s

  disjoint o s
  assert |- { s | ( s C_ ~P o /\ ( o e. s /\ A. x e. s ( o \ x ) e. s /\ A. x e. ~P s ( x ~<_ _om -> U. x e. s ) ) ) } e. _V

  proof
    vo
    cv
    #
    vs
    cv
    #
    wcel
    @0
    vx
    cv
    #
    cdif
    @1
    wcel
    vx
    @1
    wral
    @2
    com
    cdom
    wbr
    @2
    cuni
    @1
    wcel
    wi
    vx
    @1
    cpw
    wral
    w3a
    #
    vs
    @0
    cpw
    #
    cpw
    #
    crab
    #
    @1
    @4
    wss
    #
    @3
    wa
    #
    vs
    cab
    #
    cvv
    @6
    @1
    @5
    wcel
    #
    @3
    wa
    #
    vs
    cab
    @9
    @3
    vs
    @5
    df-rab
    @11
    @8
    vs
    @10
    @7
    @3
    vs
    @4
    selpw
    anbi1i
    abbii
    eqtri
    @3
    vs
    @5
    @0
    cvv
    wcel
    @4
    cvv
    wcel
    @5
    cvv
    wcel
    vo
    vex
    @0
    cvv
    pwexg
    @4
    cvv
    pwexg
    mp2b
    rabex
    eqeltrri
end
