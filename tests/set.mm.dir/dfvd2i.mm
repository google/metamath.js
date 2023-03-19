include "wvd2.mm"
include "wi.mm"
include "dfvd2.mm"
include "mpbi.mm"

theorem dfvd2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume dfvd2i.1: |- (. ph ,. ps ->. ch ).


  assert |- ( ph -> ( ps -> ch ) )

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
    dfvd2i.1
    wph
    wps
    wch
    dfvd2
    mpbi
end
