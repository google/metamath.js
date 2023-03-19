include "wi.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ralrimi.mm"
include "ralim.mm"
include "syl.mm"

theorem ralimdaa
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume ralimdaa.1: |- F/ x ph
  assume ralimdaa.2: |- ( ( ph /\ x e. A ) -> ( ps -> ch ) )


  assert |- ( ph -> ( A. x e. A ps -> A. x e. A ch ) )

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
    wral
    wch
    vx
    cA
    wral
    wi
    wph
    @0
    vx
    cA
    ralimdaa.1
    wph
    vx
    cv
    cA
    wcel
    @0
    ralimdaa.2
    ex
    ralrimi
    wps
    wch
    vx
    cA
    ralim
    syl
end
