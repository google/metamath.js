include "nfv.mm"
include "abbid.mm"

theorem abbidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume abbidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> { x | ps } = { x | ch } )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    nfv
    abbidv.1
    abbid
end
