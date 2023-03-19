include "wi.mm"
include "id.mm"
include "aleximi.mm"

theorem exim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


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
