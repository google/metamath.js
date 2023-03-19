include "a1d.mm"
include "jcad.mm"

theorem jctild
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume jctild.1: |- ( ph -> ( ps -> ch ) )
  assume jctild.2: |- ( ph -> th )


  assert |- ( ph -> ( ps -> ( th /\ ch ) ) )

  proof
    wph
    wps
    wth
    wch
    wph
    wth
    wps
    jctild.2
    a1d
    jctild.1
    jcad
end
