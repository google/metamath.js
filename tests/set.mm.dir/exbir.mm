include "wa.mm"
include "wb.mm"
include "wi.mm"
include "biimpr.mm"
include "imim2i.mm"
include "expd.mm"

theorem exbir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps ) -> ( ch <-> th ) ) -> ( ph -> ( ps -> ( th -> ch ) ) ) )

  proof
    wph
    wps
    wa
    #
    wch
    wth
    wb
    #
    wi
    wph
    wps
    wth
    wch
    wi
    #
    @1
    @2
    @0
    wch
    wth
    biimpr
    imim2i
    expd
end
