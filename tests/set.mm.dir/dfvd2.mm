include "wvd2.mm"
include "wa.mm"
include "wi.mm"
include "df-vd2.mm"
include "impexp.mm"
include "bitri.mm"

theorem dfvd2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( (. ph ,. ps ->. ch ). <-> ( ph -> ( ps -> ch ) ) )

  proof
    wph
    wps
    wch
    wvd2
    wph
    wps
    wa
    wch
    wi
    wph
    wps
    wch
    wi
    wi
    wph
    wps
    wch
    df-vd2
    wph
    wps
    wch
    impexp
    bitri
end
