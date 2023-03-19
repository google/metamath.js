include "wa.mm"
include "simpld.mm"

theorem simplld
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume simplld.1: |- ( ph -> ( ( ps /\ ch ) /\ th ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    wa
    wth
    simplld.1
    simpld
    simpld
end
