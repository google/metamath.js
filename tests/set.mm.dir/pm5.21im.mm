include "wn.mm"
include "wb.mm"
include "nbn2.mm"
include "biimpd.mm"

theorem pm5.21im
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ph -> ( -. ps -> ( ph <-> ps ) ) )

  proof
    wph
    wn
    wps
    wn
    wph
    wps
    wb
    wph
    wps
    nbn2
    biimpd
end
