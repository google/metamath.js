include "wa.mm"
include "ancom.mm"
include "exbii.mm"

theorem exancom
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x


  assert |- ( E. x ( ph /\ ps ) <-> E. x ( ps /\ ph ) )

  proof
    wph
    wps
    wa
    wps
    wph
    wa
    vx
    wph
    wps
    ancom
    exbii
end
