include "cv.mm"
include "wcel.mm"
include "pm5.32da.mm"
include "rexbidv2.mm"

theorem rexbidva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rexbidva.1: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) )

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
    wps
    wch
    rexbidva.1
    pm5.32da
    rexbidv2
end
