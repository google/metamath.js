include "cab.mm"
include "cv.mm"
include "wcel.mm"
include "bicomd.mm"
include "bj-abbi2dv.mm"
include "eqcomd.mm"

theorem bj-abbi1dv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume bj-abbi1dv.1: |- ( ph -> ( ps <-> x e. A ) )

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
    bj-abbi1dv.1
    bicomd
    bj-abbi2dv
    eqcomd
end
