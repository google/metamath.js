include "cv.mm"
include "wsbc.mm"
include "vex.mm"
include "sbcie.mm"
include "sbcbii.mm"
include "sbcco.mm"
include "3bitr3i.mm"

theorem bnj610
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let bnjwpsm: wff ps'
  assume bnj610.1: |- A e. _V
  assume bnj610.2: |- ( x = A -> ( ph <-> ps ) )
  assume bnj610.3: |- ( x = y -> ( ph <-> ps' ) )
  assume bnj610.4: |- ( y = A -> ( ps' <-> ps ) )

  disjoint A y
  disjoint ph y
  disjoint ps y
  disjoint ps' x
  disjoint x y
  assert |- ( [. A / x ]. ph <-> ps )

  proof
    wph
    vx
    vy
    cv
    #
    wsbc
    #
    vy
    cA
    wsbc
    bnjwpsm
    vy
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    wps
    @1
    bnjwpsm
    vy
    cA
    wph
    bnjwpsm
    vx
    @0
    vy
    vex
    bnj610.3
    sbcie
    sbcbii
    wph
    vx
    vy
    cA
    sbcco
    bnjwpsm
    wps
    vy
    cA
    bnj610.1
    bnj610.4
    sbcie
    3bitr3i
end
