include "wa.mm"
include "jctild.mm"
include "syl6.mm"

theorem syl6an
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
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
