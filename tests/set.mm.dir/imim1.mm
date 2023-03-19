include "wi.mm"
include "id.mm"
include "imim1d.mm"

theorem imim1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


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
