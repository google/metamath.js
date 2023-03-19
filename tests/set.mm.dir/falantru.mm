include "wfal.mm"
include "wtru.mm"
include "wa.mm"
include "fal.mm"
include "intnanr.mm"
include "bifal.mm"

theorem falantru



  assert |- ( ( F. /\ T. ) <-> F. )

  proof
    wfal
    wtru
    wa
    wfal
    wtru
    fal
    intnanr
    bifal
end
