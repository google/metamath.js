include "nfv.mm"
include "nfvd.mm"
include "weq.mm"
include "wb.mm"
include "ex.mm"
include "sbied.mm"

theorem sbiedv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume sbiedv.1: |- ( ( ph /\ x = y ) -> ( ps <-> ch ) )

  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( [ y / x ] ps <-> ch ) )

  proof
    wph
    wps
    wch
    vx
    vy
    wph
    vx
    nfv
    wph
    wch
    vx
    nfvd
    wph
    vx
    vy
    weq
    wps
    wch
    wb
    sbiedv.1
    ex
    sbied
end
