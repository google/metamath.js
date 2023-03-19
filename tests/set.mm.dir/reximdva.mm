include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "ex.mm"
include "reximdvai.mm"

theorem reximdva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume reximdva.1: |- ( ( ph /\ x e. A ) -> ( ps -> ch ) )

  disjoint ph x
  assert |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    wps
    wch
    wi
    reximdva.1
    ex
    reximdvai
end
