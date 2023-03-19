include "chmph.mm"
include "wbr.mm"
include "hmphsym.mm"
include "impbii.mm"

theorem hmphsymb
  let cJ: class J
  let cK: class K


  assert |- ( J ~= K <-> K ~= J )

  proof
    cJ
    cK
    chmph
    wbr
    cK
    cJ
    chmph
    wbr
    cJ
    cK
    hmphsym
    cK
    cJ
    hmphsym
    impbii
end
