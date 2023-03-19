include "wi.mm"
include "3exp.mm"
include "imp.mm"

theorem 3expia
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3exp.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ph /\ ps ) -> ( ch -> th ) )

  proof
    wph
    wps
    wch
    wth
    wi
    wph
    wps
    wch
    wth
    3exp.1
    3exp
    imp
end
