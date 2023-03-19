include "wvd2.mm"
include "wi.mm"
include "dfvd2.mm"
include "mpbir.mm"

theorem dfvd2ir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume dfvd2ir.1: |- ( ph -> ( ps -> ch ) )


  assert |- (. ph ,. ps ->. ch ).

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
    dfvd2ir.1
    wph
    wps
    wch
    dfvd2
    mpbir
end
