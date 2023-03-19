include "wn.mm"
include "con3d.mm"
include "syld.mm"

theorem nsyld
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  assume nsyld.1: |- ( ph -> ( ps -> -. ch ) )
  assume nsyld.2: |- ( ph -> ( ta -> ch ) )


  assert |- ( ph -> ( ps -> -. ta ) )

  proof
    wph
    wps
    wch
    wn
    wta
    wn
    nsyld.1
    wph
    wta
    wch
    nsyld.2
    con3d
    syld
end
