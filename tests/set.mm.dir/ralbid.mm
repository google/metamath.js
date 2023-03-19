include "wb.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "ralbida.mm"

theorem ralbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume ralbid.1: |- F/ x ph
  assume ralbid.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    ralbid.1
    wph
    wps
    wch
    wb
    vx
    cv
    cA
    wcel
    ralbid.2
    adantr
    ralbida
end
