include "wvd3.mm"
include "wi.mm"
include "dfvd3.mm"
include "mpbir.mm"

theorem dfvd3ir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume dfvd3ir.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- (. ph ,. ps ,. ch ->. th ).

  proof
    wph
    wps
    wch
    wth
    wvd3
    wph
    wps
    wch
    wth
    wi
    wi
    wi
    dfvd3ir.1
    wph
    wps
    wch
    wth
    dfvd3
    mpbir
end
