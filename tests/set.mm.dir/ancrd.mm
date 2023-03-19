include "idd.mm"
include "jcad.mm"

theorem ancrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
