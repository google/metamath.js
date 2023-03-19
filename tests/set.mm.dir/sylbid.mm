include "biimpd.mm"
include "syld.mm"

theorem sylbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylbid.1: |- ( ph -> ( ps <-> ch ) )
  assume sylbid.2: |- ( ph -> ( ch -> th ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    sylbid.1
    biimpd
    sylbid.2
    syld
end
