include "syld.mm"

theorem 3syld
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3syld.1: |- ( ph -> ( ps -> ch ) )
  assume 3syld.2: |- ( ph -> ( ch -> th ) )
  assume 3syld.3: |- ( ph -> ( th -> ta ) )


  assert |- ( ph -> ( ps -> ta ) )

  proof
    wph
    wps
    wth
    wta
    wph
    wps
    wch
    wth
    3syld.1
    3syld.2
    syld
    3syld.3
    syld
end
