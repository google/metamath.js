include "wi.mm"
include "id.mm"
include "aleximi.mm"

theorem exim
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x


  assert |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) )

  proof
    wph
    wps
    wi
    #
    wph
    wps
    vx
    @0
    id
    aleximi
end
