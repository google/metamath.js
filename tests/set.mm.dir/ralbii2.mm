include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "albii.mm"
include "df-ral.mm"
include "3bitr4i.mm"

theorem ralbii2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ralbii2.1: |- ( ( x e. A -> ph ) <-> ( x e. B -> ps ) )


  assert |- ( A. x e. A ph <-> A. x e. B ps )

  proof
    vx
    cv
    #
    cA
    wcel
    wph
    wi
    #
    vx
    wal
    @0
    cB
    wcel
    wps
    wi
    #
    vx
    wal
    wph
    vx
    cA
    wral
    wps
    vx
    cB
    wral
    @1
    @2
    vx
    ralbii2.1
    albii
    wph
    vx
    cA
    df-ral
    wps
    vx
    cB
    df-ral
    3bitr4i
end
