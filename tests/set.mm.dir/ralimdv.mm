include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "ralimdva.mm"

theorem ralimdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume ralimdv.1: |- ( ph -> ( ps -> ch ) )

  disjoint ph x
  assert |- ( ph -> ( A. x e. A ps -> A. x e. A ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    wph
    wps
    wch
    wi
    vx
    cv
    cA
    wcel
    ralimdv.1
    adantr
    ralimdva
end
