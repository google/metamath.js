include "wtru.mm"
include "tru.mm"
include "a1bi.mm"

theorem trut
  let wph: wff ph


  assert |- ( ph <-> ( T. -> ph ) )

  proof
    wtru
    wph
    tru
    a1bi
end
