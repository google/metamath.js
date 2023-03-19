include "biimprd.mm"
include "syld.mm"

theorem sylibrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylibrd.1: |- ( ph -> ( ps -> ch ) )
  assume sylibrd.2: |- ( ph -> ( th <-> ch ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    sylibrd.1
    wph
    wth
    wch
    sylibrd.2
    biimprd
    syld
end
