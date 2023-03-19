include "nfv.mm"
include "nfvd.mm"
include "cbv2.mm"

theorem cbvald
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume cbvald.1: |- F/ y ph
  assume cbvald.2: |- ( ph -> F/ y ps )
  assume cbvald.3: |- ( ph -> ( x = y -> ( ps <-> ch ) ) )

  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( A. x ps <-> A. y ch ) )

  proof
    wph
    wps
    wch
    vx
    vy
    wph
    vx
    nfv
    cbvald.1
    cbvald.2
    wph
    wch
    vx
    nfvd
    cbvald.3
    cbv2
end
