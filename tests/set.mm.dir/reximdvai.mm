include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "ralrimiv.mm"
include "rexim.mm"
include "syl.mm"

theorem reximdvai
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume reximdvai.1: |- ( ph -> ( x e. A -> ( ps -> ch ) ) )

  disjoint ph x
  assert |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) )

  proof
    wph
    wps
    wch
    wi
    #
    vx
    cA
    wral
    wps
    vx
    cA
    wrex
    wch
    vx
    cA
    wrex
    wi
    wph
    @0
    vx
    cA
    reximdvai.1
    ralrimiv
    wps
    wch
    vx
    cA
    rexim
    syl
end
