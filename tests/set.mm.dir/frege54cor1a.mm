include "wb.mm"
include "wn.mm"
include "wif.mm"
include "ax-frege54a.mm"
include "frege54cor0a.mm"
include "mpbi.mm"

theorem frege54cor1a
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
    ax-frege54a
    wph
    wph
    frege54cor0a
    mpbi
end
