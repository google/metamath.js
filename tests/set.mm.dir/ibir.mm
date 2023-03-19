include "bicomd.mm"
include "ibi.mm"

theorem ibir
  let wph: wff ph
  let wps: wff ps
  assume ibir.1: |- ( ph -> ( ps <-> ph ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wph
    wps
    wph
    ibir.1
    bicomd
    ibi
end
