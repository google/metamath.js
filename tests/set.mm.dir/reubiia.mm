include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weu.mm"
include "wreu.mm"
include "pm5.32i.mm"
include "eubii.mm"
include "df-reu.mm"
include "3bitr4i.mm"

theorem reubiia
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume reubiia.1: |- ( x e. A -> ( ph <-> ps ) )


  assert |- ( E! x e. A ph <-> E! x e. A ps )

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
    weu
    @0
    wps
    wa
    #
    vx
    weu
    wph
    vx
    cA
    wreu
    wps
    vx
    cA
    wreu
    @1
    @2
    vx
    @0
    wph
    wps
    reubiia.1
    pm5.32i
    eubii
    wph
    vx
    cA
    df-reu
    wps
    vx
    cA
    df-reu
    3bitr4i
end
