include "wa.mm"
include "nf5i.mm"
include "nfan.mm"
include "nf5ri.mm"

theorem hban
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume hb.1: |- ( ph -> A. x ph )
  assume hb.2: |- ( ps -> A. x ps )


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
    hb.1
    nf5i
    wps
    vx
    hb.2
    nf5i
    nfan
    nf5ri
end
