include "wi.mm"
include "wb.mm"
include "biimp.mm"
include "imim1i.mm"
include "biimpr.mm"
include "imim3i.mm"
include "syl2im.mm"

theorem bj-bi3ant
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume bj-bi3ant.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ( ( th -> ta ) -> ph ) -> ( ( ( ta -> th ) -> ps ) -> ( ( th <-> ta ) -> ch ) ) )

  proof
    wth
    wta
    wi
    #
    wph
    wi
    wth
    wta
    wb
    #
    wph
    wi
    wta
    wth
    wi
    #
    wps
    wi
    @1
    wps
    wi
    @1
    wch
    wi
    @1
    @0
    wph
    wth
    wta
    biimp
    imim1i
    @1
    @2
    wps
    wth
    wta
    biimpr
    imim1i
    wph
    wps
    wch
    @1
    bj-bi3ant.1
    imim3i
    syl2im
end
