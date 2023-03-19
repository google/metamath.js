include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "a1d.mm"
include "reximdvai.mm"

theorem reximdv
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  param cA: class A
  assume reximdv.1: |- ( ph -> ( ps -> ch ) )

  disjoint ph x
  assert |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    wph
    wps
    wch
    wi
    vx
    cv
    cA
    wcel
    reximdv.1
    a1d
    reximdvai
end
