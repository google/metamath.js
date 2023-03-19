include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cdp2.mm"
include "clt.mm"
include "wbr.mm"
include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "rpre.mm"
include "ax-mp.mm"
include "10re.mm"
include "10pos.mm"
include "ltdiv1ii.mm"
include "mpbi.mm"
include "recni.mm"
include "10nn.mm"
include "nnne0i.mm"
include "dividi.mm"
include "breqtri.mm"
include "redivcli.mm"
include "1re.mm"
include "nn0rei.mm"
include "ltadd2i.mm"
include "df-dp2.mm"
include "eqcomi.mm"
include "3brtr4i.mm"

theorem dp2ltsuc
  let cA: class A
  let cB: class B
  let cC: class C
  assume dp2lt.a: |- A e. NN0
  assume dp2lt.b: |- B e. RR+
  assume dp2ltsuc.1: |- B < ; 1 0
  assume dp2ltsuc.2: |- ( A + 1 ) = C


  assert |- _ A B < C

  proof
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
    cA
    c1
    caddc
    co
    #
    cA
    cB
    cdp2
    cC
    clt
    @1
    c1
    clt
    wbr
    @2
    @3
    clt
    wbr
    @1
    @0
    @0
    cdiv
    co
    #
    c1
    clt
    cB
    @0
    clt
    wbr
    @1
    @4
    clt
    wbr
    dp2ltsuc.1
    cB
    @0
    @0
    cB
    crp
    wcel
    cB
    cr
    wcel
    dp2lt.b
    cB
    rpre
    ax-mp
    #
    10re
    10re
    10pos
    ltdiv1ii
    mpbi
    @0
    @0
    10re
    recni
    @0
    10nn
    nnne0i
    #
    dividi
    breqtri
    @1
    c1
    cA
    cB
    @0
    @5
    10re
    @6
    redivcli
    1re
    cA
    dp2lt.a
    nn0rei
    ltadd2i
    mpbi
    cA
    cB
    df-dp2
    @3
    cC
    dp2ltsuc.2
    eqcomi
    3brtr4i
end
