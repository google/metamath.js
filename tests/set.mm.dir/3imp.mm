include "w3a.mm"
include "wa.mm"
include "df-3an.mm"
include "imp31.mm"
include "sylbi.mm"

theorem 3imp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3imp.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    w3a
    wph
    wps
    wa
    wch
    wa
    wth
    wph
    wps
    wch
    df-3an
    wph
    wps
    wch
    wth
    3imp.1
    imp31
    sylbi
end
