include "wn.mm"
include "wi.mm"
include "luk-3.mm"
include "luklem2.mm"
include "luklem1.mm"

theorem luklem3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ph -> ( ( ( -. ph -> ps ) -> ch ) -> ( th -> ch ) ) )

  proof
    wph
    wph
    wn
    #
    wth
    wn
    #
    wi
    @0
    wps
    wi
    wch
    wi
    wth
    wch
    wi
    wi
    wph
    @1
    luk-3
    @0
    wth
    wps
    wch
    luklem2
    luklem1
end
