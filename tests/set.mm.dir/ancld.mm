include "idd.mm"
include "jcad.mm"

theorem ancld
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume ancld.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps -> ( ps /\ ch ) ) )

  proof
    wph
    wps
    wps
    wch
    wph
    wps
    idd
    ancld.1
    jcad
end
