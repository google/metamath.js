include "in1.mm"
include "wi.mm"
include "syl2im.mm"
include "pm2.43i.mm"
include "syl5com.mm"
include "dfvd1ir.mm"

theorem e111
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e111.1: |- (. ph ->. ps ).
  assume e111.2: |- (. ph ->. ch ).
  assume e111.3: |- (. ph ->. th ).
  assume e111.4: |- ( ps -> ( ch -> ( th -> ta ) ) )


  assert |- (. ph ->. ta ).

  proof
    wph
    wta
    wph
    wta
    wph
    wth
    wph
    wta
    wph
    wth
    e111.3
    in1
    wph
    wth
    wta
    wi
    #
    wph
    wps
    wph
    wch
    @0
    wph
    wps
    e111.1
    in1
    wph
    wch
    e111.2
    in1
    e111.4
    syl2im
    pm2.43i
    syl5com
    pm2.43i
    dfvd1ir
end
