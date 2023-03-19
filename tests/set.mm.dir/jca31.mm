include "wa.mm"
include "jca.mm"

theorem jca31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume jca31.1: |- ( ph -> ps )
  assume jca31.2: |- ( ph -> ch )
  assume jca31.3: |- ( ph -> th )


  assert |- ( ph -> ( ( ps /\ ch ) /\ th ) )

  proof
    wph
    wps
    wch
    wa
    wth
    wph
    wps
    wch
    jca31.1
    jca31.2
    jca
    jca31.3
    jca
end
