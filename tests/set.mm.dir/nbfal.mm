include "wfal.mm"
include "fal.mm"
include "nbn.mm"

theorem nbfal
  let wph: wff ph


  assert |- ( -. ph <-> ( ph <-> F. ) )

  proof
    wfal
    wph
    fal
    nbn
end
