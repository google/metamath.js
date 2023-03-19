include "wb.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "ralbidva.mm"

theorem ralbidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume ralbidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) )

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
    ralbidv.1
    adantr
    ralbidva
end
