include "wn.mm"
include "notnot.mm"
include "notnotr.mm"
include "impbii.mm"

theorem notnotb
  let wph: wff ph


  assert |- ( ph <-> -. -. ph )

  proof
    wph
    wph
    wn
    wn
    wph
    notnot
    wph
    notnotr
    impbii
end
