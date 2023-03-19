include "orcomdd.mm"
include "cnf1dd.mm"

theorem cnf2dd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume cnf2dd.1: |- ( ph -> ( ps -> -. th ) )
  assume cnf2dd.2: |- ( ph -> ( ps -> ( ch \/ th ) ) )


  assert |- ( ph -> ( ps -> ch ) )

  proof
    wph
    wps
    wth
    wch
    cnf2dd.1
    wph
    wps
    wch
    wth
    cnf2dd.2
    orcomdd
    cnf1dd
end
