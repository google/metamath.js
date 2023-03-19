include "wa.mm"
include "jctild.mm"
include "syl6.mm"

theorem syl6an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl6an.1: |- ( ph -> ps )
  assume syl6an.2: |- ( ph -> ( ch -> th ) )
  assume syl6an.3: |- ( ( ps /\ th ) -> ta )


  assert |- ( ph -> ( ch -> ta ) )

  proof
    wph
    wch
    wps
    wth
    wa
    wta
    wph
    wch
    wth
    wps
    syl6an.2
    syl6an.1
    jctild
    syl6an.3
    syl6
end
