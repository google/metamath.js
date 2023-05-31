include "wb.mm"
include "id.mm"
include "alexbii.mm"

theorem exbi
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x


  assert |- ( A. x ( ph <-> ps ) -> ( E. x ph <-> E. x ps ) )

  proof
    wph
    wps
    wb
    #
    wph
    wps
    vx
    @0
    id
    alexbii
end
