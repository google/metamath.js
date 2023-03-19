include "cc0.mm"
include "cdp2.mm"
include "c1.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "df-dp2.mm"
include "cc.mm"
include "wcel.mm"
include "wne.mm"
include "wceq.mm"
include "10nn0.mm"
include "nn0rei.mm"
include "recni.mm"
include "0re.mm"
include "10pos.mm"
include "gtneii.mm"
include "div0.mm"
include "mp2an.mm"
include "oveq2i.mm"
include "nn0cni.mm"
include "addid1i.mm"
include "3eqtri.mm"

theorem dp20u
  let cA: class A
  assume dp20u.1: |- A e. NN0


  assert |- _ A 0 = A

  proof
    cA
    cc0
    cdp2
    cA
    cc0
    c1
    cc0
    cdc
    #
    cdiv
    co
    #
    caddc
    co
    cA
    cc0
    caddc
    co
    cA
    cA
    cc0
    df-dp2
    @1
    cc0
    cA
    caddc
    @0
    cc
    wcel
    @0
    cc0
    wne
    @1
    cc0
    wceq
    @0
    @0
    10nn0
    nn0rei
    recni
    cc0
    @0
    0re
    10pos
    gtneii
    @0
    div0
    mp2an
    oveq2i
    cA
    cA
    dp20u.1
    nn0cni
    addid1i
    3eqtri
end
