include "3imp.mm"
include "3com12.mm"

theorem 3imp21
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3imp21.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ( ps /\ ph /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    3imp21.1
    3imp
    3com12
end
