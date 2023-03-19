include "wn.mm"
include "wb.mm"
include "pm5.18.mm"
include "con2bii.mm"
include "bicomi.mm"

theorem xor3
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph <-> ps ) <-> ( ph <-> -. ps ) )

  proof
    wph
    wps
    wn
    wb
    #
    wph
    wps
    wb
    #
    wn
    @1
    @0
    wph
    wps
    pm5.18
    con2bii
    bicomi
end
