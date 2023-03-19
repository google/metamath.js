include "nfv.mm"
include "oprabbid.mm"

theorem oprabbidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oprabbidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint x z
  disjoint ph x
  disjoint ph z
  disjoint y z
  disjoint ph y
  assert |- ( ph -> { <. <. x , y >. , z >. | ps } = { <. <. x , y >. , z >. | ch } )

  proof
    wph
    wps
    wch
    vx
    vy
    vz
    wph
    vx
    nfv
    wph
    vy
    nfv
    wph
    vz
    nfv
    oprabbidv.1
    oprabbid
end
