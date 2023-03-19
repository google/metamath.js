include "wi.mm"
include "bi2.04.mm"
include "wb.mm"
include "pm5.5.mm"
include "imbi1d.mm"
include "imim2i.mm"
include "pm5.74d.mm"
include "syl5bb.mm"

theorem imim21b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ps -> ph ) -> ( ( ( ph -> ch ) -> ( ps -> th ) ) <-> ( ps -> ( ch -> th ) ) ) )

  proof
    wph
    wch
    wi
    #
    wps
    wth
    wi
    wi
    wps
    @0
    wth
    wi
    #
    wi
    wps
    wph
    wi
    #
    wps
    wch
    wth
    wi
    #
    wi
    @0
    wps
    wth
    bi2.04
    @2
    wps
    @1
    @3
    wph
    @1
    @3
    wb
    wps
    wph
    @0
    wch
    wth
    wph
    wch
    pm5.5
    imbi1d
    imim2i
    pm5.74d
    syl5bb
end
