include "wb.mm"
include "wn.mm"
include "wif.mm"
include "biid.mm"
include "ifpdfbi.mm"
include "mpbi.mm"

theorem ifpbiidcor
  let wph: wff ph


  assert |- if- ( ph , ph , -. ph )

  proof
    wph
    wph
    wb
    wph
    wph
    wph
    wn
    wif
    wph
    biid
    wph
    wph
    ifpdfbi
    mpbi
end
