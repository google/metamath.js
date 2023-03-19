include "wi.mm"
include "id.mm"
include "imim2d.mm"

theorem imim2
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) )

  proof
    wph
    wps
    wi
    #
    wph
    wps
    wch
    @0
    id
    imim2d
end
