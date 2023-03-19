include "wvd2.mm"
include "wi.mm"
include "dfvd2.mm"
include "biimpi.mm"

theorem dfvd2imp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( (. ph ,. ps ->. ch ). -> ( ph -> ( ps -> ch ) ) )

  proof
    wph
    wps
    wch
    wvd2
    wph
    wps
    wch
    wi
    wi
    wph
    wps
    wch
    dfvd2
    biimpi
end
