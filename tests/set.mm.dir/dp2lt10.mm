include "cdp2.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "df-dp2.mm"
include "c9.mm"
include "cle.mm"
include "wbr.mm"
include "9p1e10.mm"
include "breqtrri.mm"
include "cz.mm"
include "wcel.mm"
include "wb.mm"
include "nn0zi.mm"
include "9nn0.mm"
include "zleltp1.mm"
include "mp2an.mm"
include "mpbir.mm"
include "cr.mm"
include "crp.mm"
include "rpssre.mm"
include "sselii.mm"
include "10re.mm"
include "10pos.mm"
include "elrpii.mm"
include "divlt1lt.mm"
include "wa.mm"
include "wi.mm"
include "nn0rei.mm"
include "0re.mm"
include "gtneii.mm"
include "redivcli.mm"
include "pm3.2i.mm"
include "9re.mm"
include "1re.mm"
include "leltadd.mm"
include "breqtri.mm"
include "eqbrtri.mm"

theorem dp2lt10
  let cA: class A
  let cB: class B
  assume dp2lt10.a: |- A e. NN0
  assume dp2lt10.b: |- B e. RR+
  assume dp2lt10.1: |- A < ; 1 0
  assume dp2lt10.2: |- B < ; 1 0


  assert |- _ A B < ; 1 0

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
    @0
    clt
    cA
    cB
    df-dp2
    @2
    c9
    c1
    caddc
    co
    #
    @0
    clt
    cA
    c9
    cle
    wbr
    #
    @1
    c1
    clt
    wbr
    #
    @2
    @3
    clt
    wbr
    #
    @4
    cA
    @3
    clt
    wbr
    #
    cA
    @0
    @3
    clt
    dp2lt10.1
    9p1e10
    breqtrri
    cA
    cz
    wcel
    c9
    cz
    wcel
    @4
    @7
    wb
    cA
    dp2lt10.a
    nn0zi
    c9
    9nn0
    nn0zi
    cA
    c9
    zleltp1
    mp2an
    mpbir
    @5
    cB
    @0
    clt
    wbr
    #
    dp2lt10.2
    cB
    cr
    wcel
    @0
    crp
    wcel
    @5
    @8
    wb
    crp
    cr
    cB
    rpssre
    dp2lt10.b
    sselii
    #
    @0
    10re
    10pos
    elrpii
    cB
    @0
    divlt1lt
    mp2an
    mpbir
    cA
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    wa
    c9
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    wa
    @4
    @5
    wa
    @6
    wi
    @10
    @11
    cA
    dp2lt10.a
    nn0rei
    cB
    @0
    @9
    10re
    cc0
    @0
    0re
    10pos
    gtneii
    redivcli
    pm3.2i
    @12
    @13
    9re
    1re
    pm3.2i
    cA
    @1
    c9
    c1
    leltadd
    mp2an
    mp2an
    9p1e10
    breqtri
    eqbrtri
end
