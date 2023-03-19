include "cdp2.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cq.mm"
include "df-dp2.mm"
include "wcel.mm"
include "cn0.mm"
include "nn0ssq.mm"
include "sselii.mm"
include "wne.mm"
include "10nn0.mm"
include "0re.mm"
include "10pos.mm"
include "gtneii.mm"
include "qdivcl.mm"
include "mp3an.mm"
include "qaddcl.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem dp2clq
  let cA: class A
  let cB: class B
  assume dp2clq.a: |- A e. NN0
  assume dp2clq.b: |- B e. QQ


  assert |- _ A B e. QQ

  proof
    cA
    cB
    cdp2
    cA
    cB
    c1
    cc0
    cdc
    #
    cdiv
    co
    #
    caddc
    co
    #
    cq
    cA
    cB
    df-dp2
    cA
    cq
    wcel
    @1
    cq
    wcel
    #
    @2
    cq
    wcel
    cn0
    cq
    cA
    nn0ssq
    dp2clq.a
    sselii
    cB
    cq
    wcel
    @0
    cq
    wcel
    @0
    cc0
    wne
    @3
    dp2clq.b
    cn0
    cq
    @0
    nn0ssq
    10nn0
    sselii
    cc0
    @0
    0re
    10pos
    gtneii
    cB
    @0
    qdivcl
    mp3an
    cA
    @1
    qaddcl
    mp2an
    eqeltri
end
