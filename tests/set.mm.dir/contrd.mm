include "wn.mm"
include "wa.mm"
include "wi.mm"
include "jcad.mm"
include "pm2.24.mm"
include "imp.mm"
include "imim2i.mm"
include "pm2.18d.mm"
include "syl.mm"

theorem contrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume contrd.1: |- ( ph -> ( -. ps -> ch ) )
  assume contrd.2: |- ( ph -> ( -. ps -> -. ch ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wn
    #
    wch
    wch
    wn
    #
    wa
    #
    wi
    #
    wps
    wph
    @0
    wch
    @1
    contrd.1
    contrd.2
    jcad
    @3
    wps
    @2
    wps
    @0
    wch
    @1
    wps
    wch
    wps
    pm2.24
    imp
    imim2i
    pm2.18d
    syl
end
