include "wa.mm"
include "jca.mm"

theorem jca32
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume jca31.1: |- ( ph -> ps )
  assume jca31.2: |- ( ph -> ch )
  assume jca31.3: |- ( ph -> th )


  assert |- ( ph -> ( ps /\ ( ch /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    wa
    jca31.1
    wph
    wch
    wth
    jca31.2
    jca31.3
    jca
    jca
end
