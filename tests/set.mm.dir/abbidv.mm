include "nfv.mm"
include "abbid.mm"

theorem abbidv
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
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
