include "wtru.mm"
include "wa.mm"
include "truan.mm"
include "bicomi.mm"

theorem truconj
  let wph: wff ph


  assert |- ( ph <-> ( T. /\ ph ) )

  proof
    wtru
    wph
    wa
    wph
    wph
    truan
    bicomi
end
