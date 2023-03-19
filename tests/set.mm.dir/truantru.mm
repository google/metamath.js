include "wtru.mm"
include "anidm.mm"

theorem truantru



  assert |- ( ( T. /\ T. ) <-> T. )

  proof
    wtru
    anidm
end
