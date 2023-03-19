include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "alimdv.mm"
include "df-ral.mm"
include "3imtr4g.mm"

theorem ralimdv2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ralimdv2.1: |- ( ph -> ( ( x e. A -> ps ) -> ( x e. B -> ch ) ) )

  disjoint ph x
  assert |- ( ph -> ( A. x e. A ps -> A. x e. B ch ) )

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
    ralimdv2.1
    alimdv
    wps
    vx
    cA
    df-ral
    wch
    vx
    cB
    df-ral
    3imtr4g
end
