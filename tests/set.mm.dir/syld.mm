include "wi.mm"
include "a1d.mm"
include "mpdd.mm"

theorem syld
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume syld.1: |- ( ph -> ( ps -> ch ) )
  assume syld.2: |- ( ph -> ( ch -> th ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    syld.1
    wph
    wch
    wth
    wi
    wps
    syld.2
    a1d
    mpdd
end
