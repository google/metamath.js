include "wb.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "rmobidva.mm"

theorem rmobidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rmobidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> ( E* x e. A ps <-> E* x e. A ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    wph
    wps
    wch
    wb
    vx
    cv
    cA
    wcel
    rmobidv.1
    adantr
    rmobidva
end
