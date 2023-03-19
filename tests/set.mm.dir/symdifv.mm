include "cvv.mm"
include "csymdif.mm"
include "cdif.mm"
include "cun.mm"
include "df-symdif.mm"
include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "ssv.mm"
include "ssdif0.mm"
include "mpbi.mm"
include "uneq1i.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"

theorem symdifv
  let cA: class A


  assert |- ( A /_\ _V ) = ( _V \ A )

  proof
    cA
    cvv
    csymdif
    cA
    cvv
    cdif
    #
    cvv
    cA
    cdif
    #
    cun
    #
    @1
    cA
    cvv
    df-symdif
    @2
    c0
    @1
    cun
    #
    @1
    @0
    c0
    @1
    cA
    cvv
    wss
    @0
    c0
    wceq
    cA
    ssv
    cA
    cvv
    ssdif0
    mpbi
    uneq1i
    @3
    @1
    c0
    cun
    @1
    c0
    @1
    uncom
    @1
    un0
    eqtri
    eqtri
    eqtri
end
