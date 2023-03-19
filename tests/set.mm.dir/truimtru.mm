include "wtru.mm"
include "wi.mm"
include "id.mm"
include "bitru.mm"

theorem truimtru



  assert |- ( ( T. -> T. ) <-> T. )

  proof
    wtru
    wtru
    wi
    wtru
    id
    bitru
end
