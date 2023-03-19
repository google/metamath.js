include "wb.mm"
include "wi.mm"
include "imbi12.mm"
include "syl9r.mm"

theorem imbi13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ph <-> ps ) -> ( ( ch <-> th ) -> ( ( ta <-> et ) -> ( ( ph -> ( ch -> ta ) ) <-> ( ps -> ( th -> et ) ) ) ) ) )

  proof
    wch
    wth
    wb
    wta
    wet
    wb
    wch
    wta
    wi
    #
    wth
    wet
    wi
    #
    wb
    wph
    wps
    wb
    wph
    @0
    wi
    wps
    @1
    wi
    wb
    wch
    wth
    wta
    wet
    imbi12
    wph
    wps
    @0
    @1
    imbi12
    syl9r
end
