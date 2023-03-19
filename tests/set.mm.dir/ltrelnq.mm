include "cltq.mm"
include "cltpq.mm"
include "cnq.mm"
include "cxp.mm"
include "cin.mm"
include "df-ltnq.mm"
include "inss2.mm"
include "eqsstri.mm"

theorem ltrelnq
  let vx: setvar x
  let vy: setvar y


  assert |- <Q C_ ( Q. X. Q. )

  proof
    cltq
    cltpq
    cnq
    cnq
    cxp
    #
    cin
    @0
    df-ltnq
    cltpq
    @0
    inss2
    eqsstri
end
