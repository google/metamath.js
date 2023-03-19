include "w3a.mm"
include "nf5i.mm"
include "nf3an.mm"
include "nf5ri.mm"

theorem hb3an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume hb.1: |- ( ph -> A. x ph )
  assume hb.2: |- ( ps -> A. x ps )
  assume hb.3: |- ( ch -> A. x ch )


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
    hb.1
    nf5i
    wps
    vx
    hb.2
    nf5i
    wch
    vx
    hb.3
    nf5i
    nf3an
    nf5ri
end
