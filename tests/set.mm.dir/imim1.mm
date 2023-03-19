include "wi.mm"
include "id.mm"
include "imim1d.mm"

theorem imim1
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) )

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
    imim1d
end
