include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "alsc2d.mm"
include "n0.mm"
include "sylibr.mm"

theorem alscn0d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  assume alscn0d.1: |- ( ph -> A! x e. A ps )

  disjoint A x
  disjoint k x
  assert |- ( ph -> A =/= (/) )

  proof
    wph
    vx
    cv
    cA
    wcel
    vx
    wex
    cA
    c0
    wne
    wph
    wps
    vx
    cA
    alscn0d.1
    alsc2d
    vx
    cA
    n0
    sylibr
end
