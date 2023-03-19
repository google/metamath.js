include "wb.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "rabbidva.mm"

theorem rabbidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rabbidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> { x e. A | ps } = { x e. A | ch } )

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
    rabbidv.1
    adantr
    rabbidva
end
