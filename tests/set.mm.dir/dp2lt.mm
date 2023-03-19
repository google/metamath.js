include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cdp2.mm"
include "clt.mm"
include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wne.mm"
include "crp.mm"
include "rpssre.mm"
include "sselii.mm"
include "10re.mm"
include "0re.mm"
include "10pos.mm"
include "gtneii.mm"
include "redivcl.mm"
include "mp3an.mm"
include "nn0rei.mm"
include "3pm3.2i.mm"
include "wa.mm"
include "wb.mm"
include "pm3.2i.mm"
include "ltdiv1.mm"
include "mpbi.mm"
include "axltadd.mm"
include "imp.mm"
include "mp2an.mm"
include "df-dp2.mm"
include "3brtr4i.mm"

theorem dp2lt
  let cA: class A
  let cB: class B
  let cC: class C
  assume dp2lt.a: |- A e. NN0
  assume dp2lt.b: |- B e. RR+
  assume dp2lt.c: |- C e. RR+
  assume dp2lt.l: |- B < C


  assert |- _ A B < _ A C

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
    cC
    @0
    cdiv
    co
    #
    caddc
    co
    #
    cA
    cB
    cdp2
    cA
    cC
    cdp2
    clt
    @1
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    w3a
    #
    @1
    @3
    clt
    wbr
    #
    @2
    @4
    clt
    wbr
    #
    @5
    @6
    @7
    cB
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    @0
    cc0
    wne
    #
    @5
    crp
    cr
    cB
    rpssre
    dp2lt.b
    sselii
    #
    10re
    cc0
    @0
    0re
    10pos
    gtneii
    #
    cB
    @0
    redivcl
    mp3an
    cC
    cr
    wcel
    #
    @12
    @13
    @6
    crp
    cr
    cC
    rpssre
    dp2lt.c
    sselii
    #
    10re
    @15
    cC
    @0
    redivcl
    mp3an
    cA
    dp2lt.a
    nn0rei
    3pm3.2i
    cB
    cC
    clt
    wbr
    #
    @9
    dp2lt.l
    @11
    @16
    @12
    cc0
    @0
    clt
    wbr
    #
    wa
    @18
    @9
    wb
    @14
    @17
    @12
    @19
    10re
    10pos
    pm3.2i
    cB
    cC
    @0
    ltdiv1
    mp3an
    mpbi
    @8
    @9
    @10
    @1
    @3
    cA
    axltadd
    imp
    mp2an
    cA
    cB
    df-dp2
    cA
    cC
    df-dp2
    3brtr4i
end
