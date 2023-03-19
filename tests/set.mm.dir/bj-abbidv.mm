include "nfv.mm"
include "bj-abbid.mm"

theorem bj-abbidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bj-abbidv.1: |- ( ph -> ( ps <-> ch ) )

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
    bj-abbidv.1
    bj-abbid
end
