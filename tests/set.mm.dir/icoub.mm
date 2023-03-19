include "cxr.mm"
include "wcel.mm"
include "cico.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "simpl.mm"
include "icossxr.mm"
include "id.mm"
include "sseldi.mm"
include "adantl.mm"
include "simpr.mm"
include "icoltub.mm"
include "syl3anc.mm"
include "wn.mm"
include "xrltnr.mm"
include "syl.mm"
include "pm2.65da.mm"

theorem icoub
  let cA: class A
  let cB: class B


  assert |- ( A e. RR* -> -. B e. ( A [,) B ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cA
    cB
    cico
    co
    #
    wcel
    #
    cB
    cB
    clt
    wbr
    #
    @0
    @2
    wa
    @0
    cB
    cxr
    wcel
    #
    @2
    @3
    @0
    @2
    simpl
    @2
    @4
    @0
    @2
    @1
    cxr
    cB
    cA
    cB
    icossxr
    @2
    id
    sseldi
    #
    adantl
    @0
    @2
    simpr
    cA
    cB
    cB
    icoltub
    syl3anc
    @2
    @3
    wn
    #
    @0
    @2
    @4
    @6
    @5
    cB
    xrltnr
    syl
    adantl
    pm2.65da
end
