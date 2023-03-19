include "wmo.mm"
include "wa.mm"
include "simpl.mm"
include "moimi.mm"
include "moan.mm"
include "jaoi.mm"

theorem mooran1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( E* x ph \/ E* x ps ) -> E* x ( ph /\ ps ) )

  proof
    wph
    vx
    wmo
    wph
    wps
    wa
    #
    vx
    wmo
    wps
    vx
    wmo
    @0
    wph
    vx
    wph
    wps
    simpl
    moimi
    wps
    wph
    vx
    moan
    jaoi
end
