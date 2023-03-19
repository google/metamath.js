include "wb.mm"
include "wn.mm"
include "con3d.mm"
include "pm5.21im.mm"
include "syl6c.mm"
include "pm2.61d.mm"

theorem pm5.21ndd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume pm5.21ndd.1: |- ( ph -> ( ch -> ps ) )
  assume pm5.21ndd.2: |- ( ph -> ( th -> ps ) )
  assume pm5.21ndd.3: |- ( ph -> ( ps -> ( ch <-> th ) ) )


  assert |- ( ph -> ( ch <-> th ) )

  proof
    wph
    wps
    wch
    wth
    wb
    #
    pm5.21ndd.3
    wph
    wps
    wn
    wch
    wn
    wth
    wn
    @0
    wph
    wch
    wps
    pm5.21ndd.1
    con3d
    wph
    wth
    wps
    pm5.21ndd.2
    con3d
    wch
    wth
    pm5.21im
    syl6c
    pm2.61d
end
