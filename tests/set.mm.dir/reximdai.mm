include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "ralrimi.mm"
include "rexim.mm"
include "syl.mm"

theorem reximdai
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume reximdai.1: |- F/ x ph
  assume reximdai.2: |- ( ph -> ( x e. A -> ( ps -> ch ) ) )


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
    reximdai.1
    reximdai.2
    ralrimi
    wps
    wch
    vx
    cA
    rexim
    syl
end
