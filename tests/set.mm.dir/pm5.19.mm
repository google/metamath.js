include "wb.mm"
include "wn.mm"
include "biid.mm"
include "pm5.18.mm"
include "mpbi.mm"

theorem pm5.19
  let wph: wff ph


  assert |- -. ( ph <-> -. ph )

  proof
    wph
    wph
    wb
    wph
    wph
    wn
    wb
    wn
    wph
    biid
    wph
    wph
    pm5.18
    mpbi
end
