include "wb.mm"
include "biid.mm"
include "a1i.mm"

theorem biidd
  param wph: wff ph
  param wps: wff ps


  assert |- ( ph -> ( ps <-> ps ) )

  proof
    wps
    wps
    wb
    wph
    wps
    biid
    a1i
end
