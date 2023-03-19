include "wtru.mm"
include "tru.mm"
include "tbt.mm"

theorem tbtru
  let wph: wff ph


  assert |- ( ph <-> ( ph <-> T. ) )

  proof
    wtru
    wph
    tru
    tbt
end
