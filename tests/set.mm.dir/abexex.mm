include "wrex.mm"
include "cab.mm"
include "wex.mm"
include "cvv.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "df-rex.mm"
include "pm4.71ri.mm"
include "exbii.mm"
include "bitr4i.mm"
include "abbii.mm"
include "abrexex2.mm"
include "eqeltrri.mm"

theorem abexex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume abexex.1: |- A e. _V
  assume abexex.2: |- ( ph -> x e. A )
  assume abexex.3: |- { y | ph } e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- { y | E. x ph } e. _V

  proof
    wph
    vx
    cA
    wrex
    #
    vy
    cab
    wph
    vx
    wex
    #
    vy
    cab
    cvv
    @0
    @1
    vy
    @0
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    wex
    @1
    wph
    vx
    cA
    df-rex
    wph
    @3
    vx
    wph
    @2
    abexex.2
    pm4.71ri
    exbii
    bitr4i
    abbii
    wph
    vx
    vy
    cA
    abexex.1
    abexex.3
    abrexex2
    eqeltrri
end
