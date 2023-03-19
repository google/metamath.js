include "wb.mm"
include "biimpr.mm"
include "syli.mm"
include "wn.mm"
include "biimp.mm"
include "con3d.mm"
include "pm2.61d.mm"

theorem bija
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume bija.1: |- ( ph -> ( ps -> ch ) )
  assume bija.2: |- ( -. ph -> ( -. ps -> ch ) )


  assert |- ( ( ph <-> ps ) -> ch )

  proof
    wph
    wps
    wb
    #
    wps
    wch
    wps
    @0
    wph
    wch
    wph
    wps
    biimpr
    bija.1
    syli
    wps
    wn
    @0
    wph
    wn
    wch
    @0
    wph
    wps
    wph
    wps
    biimp
    con3d
    bija.2
    syli
    pm2.61d
end
