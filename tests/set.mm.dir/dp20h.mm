include "cc0.mm"
include "cdp2.mm"
include "c1.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "df-dp2.mm"
include "crp.mm"
include "wcel.mm"
include "cc.mm"
include "rpcn.mm"
include "ax-mp.mm"
include "10nn0.mm"
include "nn0cni.mm"
include "0re.mm"
include "10pos.mm"
include "gtneii.mm"
include "divcli.mm"
include "addid2i.mm"
include "eqtri.mm"

theorem dp20h
  let cA: class A
  assume dp20h.1: |- A e. RR+


  assert |- _ 0 A = ( A / ; 1 0 )

  proof
    cc0
    cA
    cdp2
    cc0
    cA
    c1
    cc0
    cdc
    #
    cdiv
    co
    #
    caddc
    co
    @1
    cc0
    cA
    df-dp2
    @1
    cA
    @0
    cA
    crp
    wcel
    cA
    cc
    wcel
    dp20h.1
    cA
    rpcn
    ax-mp
    @0
    10nn0
    nn0cni
    cc0
    @0
    0re
    10pos
    gtneii
    divcli
    addid2i
    eqtri
end
