include "idd.mm"
include "jcad.mm"

theorem ancrd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume ancrd.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps -> ( ch /\ ps ) ) )

  proof
    wph
    wps
    wch
    wps
    ancrd.1
    wph
    wps
    idd
    jcad
end
