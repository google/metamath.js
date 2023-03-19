include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wrmo.mm"
include "pm5.32i.mm"
include "mobii.mm"
include "df-rmo.mm"
include "3bitr4i.mm"

theorem rmobiia
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume rmobiia.1: |- ( x e. A -> ( ph <-> ps ) )


  assert |- ( E* x e. A ph <-> E* x e. A ps )

  proof
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    wmo
    @0
    wps
    wa
    #
    vx
    wmo
    wph
    vx
    cA
    wrmo
    wps
    vx
    cA
    wrmo
    @1
    @2
    vx
    @0
    wph
    wps
    rmobiia.1
    pm5.32i
    mobii
    wph
    vx
    cA
    df-rmo
    wps
    vx
    cA
    df-rmo
    3bitr4i
end
