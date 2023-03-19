include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "sylbir.mm"
include "ralrimiva.mm"

theorem bnj1459
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume bnj1459.1: |- ( ps <-> ( ph /\ x e. A ) )
  assume bnj1459.2: |- ( ps -> ch )

  disjoint ph x
  assert |- ( ph -> A. x e. A ch )

  proof
    wph
    wch
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    wa
    wps
    wch
    bnj1459.1
    bnj1459.2
    sylbir
    ralrimiva
end
