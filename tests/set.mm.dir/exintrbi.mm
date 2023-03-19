include "wi.mm"
include "wa.mm"
include "abai.mm"
include "rbaibr.mm"
include "alexbii.mm"

theorem exintrbi
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x


  assert |- ( A. x ( ph -> ps ) -> ( E. x ph <-> E. x ( ph /\ ps ) ) )

  proof
    wph
    wps
    wi
    #
    wph
    wph
    wps
    wa
    #
    vx
    @1
    wph
    @0
    wph
    wps
    abai
    rbaibr
    alexbii
end
