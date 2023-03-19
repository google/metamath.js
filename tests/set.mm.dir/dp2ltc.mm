include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cdp2.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wb.mm"
include "rpssre.mm"
include "sselii.mm"
include "10re.mm"
include "10pos.mm"
include "elrp.mm"
include "mpbir2an.mm"
include "divlt1lt.mm"
include "mp2an.mm"
include "mpbir.mm"
include "gt0ne0ii.mm"
include "redivcli.mm"
include "1re.mm"
include "nn0rei.mm"
include "ltadd2.mm"
include "mp3an.mm"
include "mpbi.mm"
include "cz.mm"
include "nn0zi.mm"
include "zltp1le.mm"
include "readdcli.mm"
include "ltletri.mm"
include "wa.mm"
include "pm3.2i.mm"
include "rpdivcl.mm"
include "ax-mp.mm"
include "ltaddrp.mm"
include "lttri.mm"
include "df-dp2.mm"
include "3brtr4i.mm"

theorem dp2ltc
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume dp2lt.a: |- A e. NN0
  assume dp2lt.b: |- B e. RR+
  assume dp2ltc.c: |- C e. NN0
  assume dp2ltc.d: |- D e. RR+
  assume dp2ltc.s: |- B < ; 1 0
  assume dp2ltc.l: |- A < C


  assert |- _ A B < _ C D

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
    cC
    cD
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
    cC
    cD
    cdp2
    clt
    @2
    cC
    clt
    wbr
    #
    cC
    @4
    clt
    wbr
    #
    @2
    @4
    clt
    wbr
    @2
    cA
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @7
    cC
    cle
    wbr
    #
    @5
    @1
    c1
    clt
    wbr
    #
    @8
    @10
    cB
    @0
    clt
    wbr
    #
    dp2ltc.s
    cB
    cr
    wcel
    @0
    crp
    wcel
    #
    @10
    @11
    wb
    crp
    cr
    cB
    rpssre
    dp2lt.b
    sselii
    #
    @12
    @0
    cr
    wcel
    cc0
    @0
    clt
    wbr
    10re
    10pos
    @0
    elrp
    mpbir2an
    #
    cB
    @0
    divlt1lt
    mp2an
    mpbir
    @1
    cr
    wcel
    c1
    cr
    wcel
    cA
    cr
    wcel
    @10
    @8
    wb
    cB
    @0
    @13
    10re
    @0
    10re
    10pos
    gt0ne0ii
    #
    redivcli
    #
    1re
    cA
    dp2lt.a
    nn0rei
    #
    @1
    c1
    cA
    ltadd2
    mp3an
    mpbi
    cA
    cC
    clt
    wbr
    #
    @9
    dp2ltc.l
    cA
    cz
    wcel
    cC
    cz
    wcel
    @18
    @9
    wb
    cA
    dp2lt.a
    nn0zi
    cC
    dp2ltc.c
    nn0zi
    cA
    cC
    zltp1le
    mp2an
    mpbi
    @2
    @7
    cC
    cA
    @1
    @17
    @16
    readdcli
    #
    cA
    c1
    @17
    1re
    readdcli
    cC
    dp2ltc.c
    nn0rei
    #
    ltletri
    mp2an
    cC
    cr
    wcel
    @3
    crp
    wcel
    #
    @6
    @20
    cD
    crp
    wcel
    #
    @12
    wa
    @21
    @22
    @12
    dp2ltc.d
    @14
    pm3.2i
    cD
    @0
    rpdivcl
    ax-mp
    cC
    @3
    ltaddrp
    mp2an
    @2
    cC
    @4
    @19
    @20
    cC
    @3
    @20
    cD
    @0
    crp
    cr
    cD
    rpssre
    dp2ltc.d
    sselii
    10re
    @15
    redivcli
    readdcli
    lttri
    mp2an
    cA
    cB
    df-dp2
    cC
    cD
    df-dp2
    3brtr4i
end
