include "cab.mm"
include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "vex.mm"
include "elab.mm"
include "anbi1i.mm"
include "exbii.mm"
include "bitri.mm"

theorem rexab
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume ralab.1: |- ( y = x -> ( ph <-> ps ) )

  disjoint x y
  disjoint ps y
  disjoint A y
  assert |- ( E. x e. { y | ph } ch <-> E. x ( ps /\ ch ) )

  proof
    wch
    vx
    wph
    vy
    cab
    #
    wrex
    vx
    cv
    #
    @0
    wcel
    #
    wch
    wa
    #
    vx
    wex
    wps
    wch
    wa
    #
    vx
    wex
    wch
    vx
    @0
    df-rex
    @3
    @4
    vx
    @2
    wps
    wch
    wph
    wps
    vy
    @1
    vx
    vex
    ralab.1
    elab
    anbi1i
    exbii
    bitri
end
