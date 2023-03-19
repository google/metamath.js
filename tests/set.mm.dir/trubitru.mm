include "wtru.mm"
include "wb.mm"
include "biid.mm"
include "bitru.mm"

theorem trubitru



  assert |- ( ( T. <-> T. ) <-> T. )

  proof
    wtru
    wtru
    wb
    wtru
    biid
    bitru
end
