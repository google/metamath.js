include "wn.mm"
include "notnot.mm"
include "syl6.mm"
include "cnf1dd.mm"

theorem cnfn1dd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume cnfn1dd.1: |- ( ph -> ( ps -> ch ) )
  assume cnfn1dd.2: |- ( ph -> ( ps -> ( -. ch \/ th ) ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wn
    #
    wth
    wph
    wps
    wch
    @0
    wn
    cnfn1dd.1
    wch
    notnot
    syl6
    cnfn1dd.2
    cnf1dd
end
