include "sylibrd.mm"
include "sylbid.mm"

theorem 3imtr4d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3imtr4d.1: |- ( ph -> ( ps -> ch ) )
  assume 3imtr4d.2: |- ( ph -> ( th <-> ps ) )
  assume 3imtr4d.3: |- ( ph -> ( ta <-> ch ) )


  assert |- ( ph -> ( th -> ta ) )

  proof
    wph
    wth
    wps
    wta
    3imtr4d.2
    wph
    wps
    wch
    wta
    3imtr4d.1
    3imtr4d.3
    sylibrd
    sylbid
end
