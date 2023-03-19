include "wn.mm"
include "wb.mm"
include "nbbn.mm"
include "bicomi.mm"

theorem notbinot2
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph <-> ps ) <-> ( -. ph <-> ps ) )

  proof
    wph
    wn
    wps
    wb
    wph
    wps
    wb
    wn
    wph
    wps
    nbbn
    bicomi
end
