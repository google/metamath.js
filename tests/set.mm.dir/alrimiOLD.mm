include "nfriOLD.mm"
include "alrimih.mm"

theorem alrimiOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume alrimiOLD.1: |- nfOLD x ph
  assume alrimiOLD.2: |- ( ph -> ps )


  assert |- ( ph -> A. x ps )

  proof
    wph
    wps
    vx
    wph
    vx
    alrimiOLD.1
    nfriOLD
    alrimiOLD.2
    alrimih
end
