include "biimpri.mm"
include "syl6.mm"

theorem syl6ibr
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume syl6ibr.1: |- ( ph -> ( ps -> ch ) )
  assume syl6ibr.2: |- ( th <-> ch )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    syl6ibr.1
    wth
    wch
    syl6ibr.2
    biimpri
    syl6
end
