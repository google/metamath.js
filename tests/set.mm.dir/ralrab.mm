include "wi.mm"
include "crab.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "elrab.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "ralbii2.mm"

theorem ralrab
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
  assert |- ( A. x e. { y e. A | ph } ch <-> A. x e. A ( ps -> ch ) )

  proof
    wch
    wps
    wch
    wi
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
    wi
    @2
    cA
    wcel
    #
    wps
    wa
    #
    wch
    wi
    @4
    @0
    wi
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
    imbi1i
    @4
    wps
    wch
    impexp
    bitri
    ralbii2
end
