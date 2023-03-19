include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "albidv.mm"
include "df-ral.mm"
include "3bitr4g.mm"

theorem ralbidv2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ralbidv2.1: |- ( ph -> ( ( x e. A -> ps ) <-> ( x e. B -> ch ) ) )

  disjoint ph x
  assert |- ( ph -> ( A. x e. A ps <-> A. x e. B ch ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    wps
    wi
    #
    vx
    wal
    @0
    cB
    wcel
    wch
    wi
    #
    vx
    wal
    wps
    vx
    cA
    wral
    wch
    vx
    cB
    wral
    wph
    @1
    @2
    vx
    ralbidv2.1
    albidv
    wps
    vx
    cA
    df-ral
    wch
    vx
    cB
    df-ral
    3bitr4g
end
