include "wtru.mm"
include "oridm.mm"

theorem truortru



  assert |- ( ( T. \/ T. ) <-> T. )

  proof
    wtru
    oridm
end
