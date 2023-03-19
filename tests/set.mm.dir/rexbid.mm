include "wb.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "rexbida.mm"

theorem rexbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rexbid.1: |- F/ x ph
  assume rexbid.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    rexbid.1
    wph
    wps
    wch
    wb
    vx
    cv
    cA
    wcel
    rexbid.2
    adantr
    rexbida
end
