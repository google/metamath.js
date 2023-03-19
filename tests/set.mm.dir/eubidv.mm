include "nfv.mm"
include "eubid.mm"

theorem eubidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume eubidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> ( E! x ps <-> E! x ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    nfv
    eubidv.1
    eubid
end
