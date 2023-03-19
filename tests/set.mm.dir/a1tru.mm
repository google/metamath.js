include "wtru.mm"
include "tru.mm"
include "a1i.mm"

theorem a1tru
  let wph: wff ph


  assert |- ( ph -> T. )

  proof
    wtru
    wph
    tru
    a1i
end
