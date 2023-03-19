include "c0.mm"
include "cinf.mm"
include "ccnv.mm"
include "csup.mm"
include "df-inf.mm"
include "sup00.mm"
include "eqtri.mm"

theorem inf00
  let cB: class B
  let cR: class R


  assert |- inf ( B , (/) , R ) = (/)

  proof
    cB
    c0
    cR
    cinf
    cB
    c0
    cR
    ccnv
    #
    csup
    c0
    cB
    c0
    cR
    df-inf
    cB
    @0
    sup00
    eqtri
end
