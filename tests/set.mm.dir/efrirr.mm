include "cep.mm"
include "wfr.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "frirr.mm"
include "wb.mm"
include "epelg.mm"
include "adantl.mm"
include "mtbid.mm"
include "pm2.01da.mm"

theorem efrirr
  let cA: class A


  assert |- ( _E Fr A -> -. A e. A )

  proof
    cA
    cep
    wfr
    #
    cA
    cA
    wcel
    #
    @0
    @1
    wa
    cA
    cA
    cep
    wbr
    #
    @1
    cA
    cA
    cep
    frirr
    @1
    @2
    @1
    wb
    @0
    cA
    cA
    cA
    epelg
    adantl
    mtbid
    pm2.01da
end
