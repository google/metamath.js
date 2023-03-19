include "cv.mm"
include "wcel.mm"
include "pm5.74da.mm"
include "ralbidv2.mm"

theorem ralbidva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume ralbidva.1: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) )

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
    ralbidva.1
    pm5.74da
    ralbidv2
end
