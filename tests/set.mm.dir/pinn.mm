include "cnpi.mm"
include "com.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "df-ni.mm"
include "difss.mm"
include "eqsstri.mm"
include "sseli.mm"

theorem pinn
  let cA: class A


  assert |- ( A e. N. -> A e. _om )

  proof
    cnpi
    com
    cA
    cnpi
    com
    c0
    csn
    #
    cdif
    com
    df-ni
    com
    @0
    difss
    eqsstri
    sseli
end
