include "wa.mm"
include "dfvd2i.mm"
include "imp.mm"
include "wi.mm"
include "syl2im.mm"
include "pm2.43i.mm"
include "syl5com.mm"
include "ex.mm"
include "dfvd2ir.mm"

theorem e222
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e222.1: |- (. ph ,. ps ->. ch ).
  assume e222.2: |- (. ph ,. ps ->. th ).
  assume e222.3: |- (. ph ,. ps ->. ta ).
  assume e222.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- (. ph ,. ps ->. et ).

  proof
    wph
    wps
    wet
    wph
    wps
    wet
    wph
    wps
    wa
    #
    wet
    @0
    wta
    @0
    wet
    wph
    wps
    wta
    wph
    wps
    wta
    e222.3
    dfvd2i
    imp
    @0
    wta
    wet
    wi
    #
    @0
    wch
    @0
    wth
    @1
    wph
    wps
    wch
    wph
    wps
    wch
    e222.1
    dfvd2i
    imp
    wph
    wps
    wth
    wph
    wps
    wth
    e222.2
    dfvd2i
    imp
    e222.4
    syl2im
    pm2.43i
    syl5com
    pm2.43i
    ex
    dfvd2ir
end
