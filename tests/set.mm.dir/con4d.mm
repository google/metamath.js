include "wn.mm"
include "wi.mm"
include "con4.mm"
include "syl.mm"

theorem con4d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume con4d.1: |- ( ph -> ( -. ps -> -. ch ) )


  assert |- ( ph -> ( ch -> ps ) )

  proof
    wph
    wps
    wn
    wch
    wn
    wi
    wch
    wps
    wi
    con4d.1
    wps
    wch
    con4
    syl
end
