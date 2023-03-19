include "wb.mm"
include "pm5.1im.mm"
include "biimp.mm"
include "com12.mm"
include "impbid.mm"

theorem pm5.501
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps <-> ( ph <-> ps ) ) )

  proof
    wph
    wps
    wph
    wps
    wb
    #
    wph
    wps
    pm5.1im
    @0
    wph
    wps
    wph
    wps
    biimp
    com12
    impbid
end
