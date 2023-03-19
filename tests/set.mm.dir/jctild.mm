include "a1d.mm"
include "jcad.mm"

theorem jctild
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
