include "wa.mm"
include "nfiOLD.mm"
include "nfanOLDOLD.mm"
include "nfriOLD.mm"

theorem hbanOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume hbOLD.1: |- ( ph -> A. x ph )
  assume hbOLD.2: |- ( ps -> A. x ps )


  assert |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) )

  proof
    wph
    wps
    wa
    vx
    wph
    wps
    vx
    wph
    vx
    hbOLD.1
    nfiOLD
    wps
    vx
    hbOLD.2
    nfiOLD
    nfanOLDOLD
    nfriOLD
end
