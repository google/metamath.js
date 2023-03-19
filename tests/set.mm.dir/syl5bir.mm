include "biimpri.mm"
include "syl5.mm"

theorem syl5bir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syl5bir.1: |- ( ps <-> ph )
  assume syl5bir.2: |- ( ch -> ( ps -> th ) )


  assert |- ( ch -> ( ph -> th ) )

  proof
    wph
    wps
    wch
    wth
    wps
    wph
    syl5bir.1
    biimpri
    syl5bir.2
    syl5
end
