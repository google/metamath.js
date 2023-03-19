include "biid.mm"

theorem axfrege54a
  let wph: wff ph


  assert |- ( ph <-> ph )

  proof
    wph
    biid
end
