include "nfv.mm"
include "mobid.mm"

theorem mobidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume mobidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> ( E* x ps <-> E* x ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    nfv
    mobidv.1
    mobid
end
