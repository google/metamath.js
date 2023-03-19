include "nfv.mm"
include "nfvd.mm"
include "weq.mm"
include "wb.mm"
include "ex.mm"
include "cbvald.mm"

theorem cbvaldvaOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume cbvaldva.1: |- ( ( ph /\ x = y ) -> ( ps <-> ch ) )

  disjoint ps y
  disjoint ch x
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( A. x ps <-> A. y ch ) )

  proof
    wph
    wps
    wch
    vx
    vy
    wph
    vy
    nfv
    wph
    wps
    vy
    nfvd
    wph
    vx
    vy
    weq
    wps
    wch
    wb
    cbvaldva.1
    ex
    cbvald
end
