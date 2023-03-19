include "cab.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "vex.mm"
include "elab.mm"
include "imbi1i.mm"
include "albii.mm"
include "bitri.mm"

theorem ralab
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
  assert |- ( A. x e. { y | ph } ch <-> A. x ( ps -> ch ) )

  proof
    wch
    vx
    wph
    vy
    cab
    #
    wral
    vx
    cv
    #
    @0
    wcel
    #
    wch
    wi
    #
    vx
    wal
    wps
    wch
    wi
    #
    vx
    wal
    wch
    vx
    @0
    df-ral
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
    imbi1i
    albii
    bitri
end
