include "nfv.mm"
include "cbvsbc.mm"

theorem cbvsbcv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume cbvsbcv.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint ph y
  disjoint ps x
  assert |- ( [. A / x ]. ph <-> [. A / y ]. ps )

  proof
    wph
    wps
    vx
    vy
    cA
    wph
    vy
    nfv
    wps
    vx
    nfv
    cbvsbcv.1
    cbvsbc
end
