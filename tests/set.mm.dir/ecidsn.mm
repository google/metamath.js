include "cid.mm"
include "cec.mm"
include "csn.mm"
include "cima.mm"
include "df-ec.mm"
include "imai.mm"
include "eqtri.mm"

theorem ecidsn
  let cA: class A


  assert |- [ A ] _I = { A }

  proof
    cA
    cid
    cec
    cid
    cA
    csn
    #
    cima
    @0
    cA
    cid
    df-ec
    @0
    imai
    eqtri
end
