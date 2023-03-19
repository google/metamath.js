include "wb.mm"
include "wn.mm"
include "nbbn.mm"
include "bicomi.mm"
include "con1bii.mm"

theorem notbinot1
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( -. ph <-> ps ) <-> ( ph <-> ps ) )

  proof
    wph
    wps
    wb
    #
    wph
    wn
    wps
    wb
    #
    @1
    @0
    wn
    wph
    wps
    nbbn
    bicomi
    con1bii
end
