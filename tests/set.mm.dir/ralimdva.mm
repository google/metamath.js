include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "ex.mm"
include "a2d.mm"
include "ralimdv2.mm"

theorem ralimdva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume ralimdva.1: |- ( ( ph /\ x e. A ) -> ( ps -> ch ) )

  disjoint ph x
  assert |- ( ph -> ( A. x e. A ps -> A. x e. A ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    cA
    wph
    vx
    cv
    cA
    wcel
    #
    wps
    wch
    wph
    @0
    wps
    wch
    wi
    ralimdva.1
    ex
    a2d
    ralimdv2
end
