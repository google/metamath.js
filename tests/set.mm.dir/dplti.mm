include "cdp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "rpre.mm"
include "ax-mp.mm"
include "dpval2.mm"
include "wbr.mm"
include "wb.mm"
include "wa.mm"
include "10re.mm"
include "10pos.mm"
include "pm3.2i.mm"
include "elrp.mm"
include "mpbir.mm"
include "divlt1lt.mm"
include "mp2an.mm"
include "0re.mm"
include "gtneii.mm"
include "redivcli.mm"
include "1re.mm"
include "cn0.mm"
include "nn0ssre.mm"
include "sselii.mm"
include "ltadd2i.mm"
include "mpbi.mm"
include "eqbrtri.mm"
include "breqtri.mm"

theorem dplti
  let cA: class A
  let cB: class B
  let cC: class C
  assume dplti.a: |- A e. NN0
  assume dplti.b: |- B e. RR+
  assume dplti.c: |- C e. NN0
  assume dplti.1: |- B < ; 1 0
  assume dplti.2: |- ( A + 1 ) = C


  assert |- ( A . B ) < C

  proof
    cA
    cB
    cdp
    co
    #
    cA
    c1
    caddc
    co
    #
    cC
    clt
    @0
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
    @1
    clt
    cA
    cB
    dplti.a
    cB
    crp
    wcel
    cB
    cr
    wcel
    #
    dplti.b
    cB
    rpre
    ax-mp
    #
    dpval2
    @3
    c1
    clt
    wbr
    #
    @4
    @1
    clt
    wbr
    @7
    cB
    @2
    clt
    wbr
    #
    dplti.1
    @5
    @2
    crp
    wcel
    #
    @7
    @8
    wb
    @6
    @9
    @2
    cr
    wcel
    #
    cc0
    @2
    clt
    wbr
    #
    wa
    @10
    @11
    10re
    10pos
    pm3.2i
    @2
    elrp
    mpbir
    cB
    @2
    divlt1lt
    mp2an
    mpbir
    @3
    c1
    cA
    cB
    @2
    @6
    10re
    cc0
    @2
    0re
    10pos
    gtneii
    redivcli
    1re
    cn0
    cr
    cA
    nn0ssre
    dplti.a
    sselii
    ltadd2i
    mpbi
    eqbrtri
    dplti.2
    breqtri
end
