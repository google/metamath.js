include "wn.mm"
include "wb.mm"
include "pm5.501.mm"
include "notbi.mm"
include "syl6bbr.mm"

theorem nbn2
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ph -> ( -. ps <-> ( ph <-> ps ) ) )

  proof
    wph
    wn
    #
    wps
    wn
    #
    @0
    @1
    wb
    wph
    wps
    wb
    @0
    @1
    pm5.501
    wph
    wps
    notbi
    syl6bbr
end
