include "wa.mm"
include "crab.mm"
include "cv.mm"
include "wcel.mm"
include "elrab.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "rexbii2.mm"

theorem rexrab
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume ralab.1: |- ( y = x -> ( ph <-> ps ) )

  disjoint x y
  disjoint A y
  disjoint ps y
  assert |- ( E. x e. { y e. A | ph } ch <-> E. x e. A ( ps /\ ch ) )

  proof
    wch
    wps
    wch
    wa
    #
    vx
    wph
    vy
    cA
    crab
    #
    cA
    vx
    cv
    #
    @1
    wcel
    #
    wch
    wa
    @2
    cA
    wcel
    #
    wps
    wa
    #
    wch
    wa
    @4
    @0
    wa
    @3
    @5
    wch
    wph
    wps
    vy
    @2
    cA
    ralab.1
    elrab
    anbi1i
    @4
    wps
    wch
    anass
    bitri
    rexbii2
end
