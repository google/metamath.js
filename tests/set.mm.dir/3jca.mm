include "wa.mm"
include "w3a.mm"
include "jca31.mm"
include "df-3an.mm"
include "sylibr.mm"

theorem 3jca
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3jca.1: |- ( ph -> ps )
  assume 3jca.2: |- ( ph -> ch )
  assume 3jca.3: |- ( ph -> th )


  assert |- ( ph -> ( ps /\ ch /\ th ) )

  proof
    wph
    wps
    wch
    wa
    wth
    wa
    wps
    wch
    wth
    w3a
    wph
    wps
    wch
    wth
    3jca.1
    3jca.2
    3jca.3
    jca31
    wps
    wch
    wth
    df-3an
    sylibr
end
