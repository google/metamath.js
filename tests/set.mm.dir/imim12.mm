include "wi.mm"
include "imim2.mm"
include "com13.mm"
include "imim2i.mm"
include "com24.mm"

theorem imim12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ps ) -> ( ( ch -> th ) -> ( ( ps -> ch ) -> ( ph -> th ) ) ) )

  proof
    wph
    wps
    wi
    wph
    wps
    wch
    wi
    #
    wch
    wth
    wi
    #
    wth
    wps
    @0
    @1
    wth
    wi
    wi
    wph
    @1
    @0
    wps
    wth
    wch
    wth
    wps
    imim2
    com13
    imim2i
    com24
end
