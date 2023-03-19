include "cab.mm"
include "cv.mm"
include "wcel.mm"
include "bicomd.mm"
include "abbi2dv.mm"
include "eqcomd.mm"

theorem abbi1dv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume abbi1dv.1: |- ( ph -> ( ps <-> x e. A ) )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> { x | ps } = A )

  proof
    wph
    cA
    wps
    vx
    cab
    wph
    wps
    vx
    cA
    wph
    wps
    vx
    cv
    cA
    wcel
    abbi1dv.1
    bicomd
    abbi2dv
    eqcomd
end
