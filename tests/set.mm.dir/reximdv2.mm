include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "eximdv.mm"
include "df-rex.mm"
include "3imtr4g.mm"

theorem reximdv2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume reximdv2.1: |- ( ph -> ( ( x e. A /\ ps ) -> ( x e. B /\ ch ) ) )

  disjoint ph x
  assert |- ( ph -> ( E. x e. A ps -> E. x e. B ch ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    wps
    wa
    #
    vx
    wex
    @0
    cB
    wcel
    wch
    wa
    #
    vx
    wex
    wps
    vx
    cA
    wrex
    wch
    vx
    cB
    wrex
    wph
    @1
    @2
    vx
    reximdv2.1
    eximdv
    wps
    vx
    cA
    df-rex
    wch
    vx
    cB
    df-rex
    3imtr4g
end
