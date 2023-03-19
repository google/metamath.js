include "w3a.mm"
include "dfvd3i.mm"
include "3imp.mm"
include "wi.mm"
include "syl2im.mm"
include "pm2.43i.mm"
include "syl5com.mm"
include "3exp.mm"
include "dfvd3ir.mm"

theorem e333
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume e333.1: |- (. ph ,. ps ,. ch ->. th ).
  assume e333.2: |- (. ph ,. ps ,. ch ->. ta ).
  assume e333.3: |- (. ph ,. ps ,. ch ->. et ).
  assume e333.4: |- ( th -> ( ta -> ( et -> ze ) ) )


  assert |- (. ph ,. ps ,. ch ->. ze ).

  proof
    wph
    wps
    wch
    wze
    wph
    wps
    wch
    wze
    wph
    wps
    wch
    w3a
    #
    wze
    @0
    wet
    @0
    wze
    wph
    wps
    wch
    wet
    wph
    wps
    wch
    wet
    e333.3
    dfvd3i
    3imp
    @0
    wet
    wze
    wi
    #
    @0
    wth
    @0
    wta
    @1
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    e333.1
    dfvd3i
    3imp
    wph
    wps
    wch
    wta
    wph
    wps
    wch
    wta
    e333.2
    dfvd3i
    3imp
    e333.4
    syl2im
    pm2.43i
    syl5com
    pm2.43i
    3exp
    dfvd3ir
end
