include "w3a.mm"
include "nfiOLD.mm"
include "nf3anOLD.mm"
include "nfriOLD.mm"

theorem hb3anOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume hbOLD.1: |- ( ph -> A. x ph )
  assume hbOLD.2: |- ( ps -> A. x ps )
  assume hbOLD.3: |- ( ch -> A. x ch )


  assert |- ( ( ph /\ ps /\ ch ) -> A. x ( ph /\ ps /\ ch ) )

  proof
    wph
    wps
    wch
    w3a
    vx
    wph
    wps
    wch
    vx
    wph
    vx
    hbOLD.1
    nfiOLD
    wps
    vx
    hbOLD.2
    nfiOLD
    wch
    vx
    hbOLD.3
    nfiOLD
    nf3anOLD
    nfriOLD
end
