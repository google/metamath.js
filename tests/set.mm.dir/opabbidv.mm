include "nfv.mm"
include "opabbid.mm"

theorem opabbidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume opabbidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  disjoint ph y
  assert |- ( ph -> { <. x , y >. | ps } = { <. x , y >. | ch } )

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
    vy
    nfv
    opabbidv.1
    opabbid
end
