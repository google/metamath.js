include "cpw.mm"
include "wrex.mm"
include "cab.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "wcel.mm"
include "df-rex.mm"
include "selpw.mm"
include "anbi1i.mm"
include "exbii.mm"
include "bitri.mm"
include "abbii.mm"
include "pwex.mm"
include "abrexex2.mm"
include "eqeltrri.mm"

theorem abexssex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume abrexex2.1: |- A e. _V
  assume abrexex2.2: |- { y | ph } e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- { y | E. x ( x C_ A /\ ph ) } e. _V

  proof
    wph
    vx
    cA
    cpw
    #
    wrex
    #
    vy
    cab
    vx
    cv
    #
    cA
    wss
    #
    wph
    wa
    #
    vx
    wex
    #
    vy
    cab
    cvv
    @1
    @5
    vy
    @1
    @2
    @0
    wcel
    #
    wph
    wa
    #
    vx
    wex
    @5
    wph
    vx
    @0
    df-rex
    @7
    @4
    vx
    @6
    @3
    wph
    vx
    cA
    selpw
    anbi1i
    exbii
    bitri
    abbii
    wph
    vx
    vy
    @0
    cA
    abrexex2.1
    pwex
    abrexex2.2
    abrexex2
    eqeltrri
end
