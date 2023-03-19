include "wn.mm"
include "notnot.mm"
include "syl6.mm"
include "cnf2dd.mm"

theorem cnfn2dd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume cnfn2dd.1: |- ( ph -> ( ps -> th ) )
  assume cnfn2dd.2: |- ( ph -> ( ps -> ( ch \/ -. th ) ) )


  assert |- ( ph -> ( ps -> ch ) )

  proof
    wph
    wps
    wch
    wth
    wn
    #
    wph
    wps
    wth
    @0
    wn
    cnfn2dd.1
    wth
    notnot
    syl6
    cnfn2dd.2
    cnf2dd
end
