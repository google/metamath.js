include "wtru.mm"
include "wa.mm"
include "tru.mm"
include "biantrur.mm"
include "bicomi.mm"

theorem truan
  let wph: wff ph


  assert |- ( ( T. /\ ph ) <-> ph )

  proof
    wph
    wtru
    wph
    wa
    wtru
    wph
    tru
    biantrur
    bicomi
end
