include "wtru.mm"
include "wi.mm"
include "tru.mm"
include "id.mm"
include "2th.mm"

theorem dftru2
  let wph: wff ph


  assert |- ( T. <-> ( ph -> ph ) )

  proof
    wtru
    wph
    wph
    wi
    tru
    wph
    id
    2th
end
