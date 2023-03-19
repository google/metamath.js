include "wn.mm"
include "wb.mm"
include "pm5.21im.mm"
include "imp.mm"

theorem pm5.21
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph /\ -. ps ) -> ( ph <-> ps ) )

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
    pm5.21im
    imp
end
