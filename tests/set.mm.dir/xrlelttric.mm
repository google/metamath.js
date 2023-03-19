include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wo.mm"
include "wn.mm"
include "pm2.1.mm"
include "xrlenlt.mm"
include "orbi1d.mm"
include "mpbiri.mm"

theorem xrlelttric
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A <_ B \/ B < A ) )

  proof
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    wa
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    clt
    wbr
    #
    wo
    @2
    wn
    #
    @2
    wo
    @2
    pm2.1
    @0
    @1
    @3
    @2
    cA
    cB
    xrlenlt
    orbi1d
    mpbiri
end
