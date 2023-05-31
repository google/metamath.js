include "wb.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "rexbidva.mm"

theorem rexbidv
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  param cA: class A
  assume rexbidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) )

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
    rexbidv.1
    adantr
    rexbidva
end
