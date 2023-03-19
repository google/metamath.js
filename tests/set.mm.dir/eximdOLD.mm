include "nfriOLD.mm"
include "eximdh.mm"

theorem eximdOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume eximdOLD.1: |- nfOLD x ph
  assume eximdOLD.2: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( E. x ps -> E. x ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    eximdOLD.1
    nfriOLD
    eximdOLD.2
    eximdh
end
