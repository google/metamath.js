include "cdp2.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cdiv.mm"
include "cdp.mm"
include "wne.mm"
include "wceq.mm"
include "0re.mm"
include "10pos.mm"
include "gtneii.mm"
include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "rpdp2cl.mm"
include "rpre.mm"
include "ax-mp.mm"
include "recni.mm"
include "cc.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "10re.mm"
include "pm3.2i.mm"
include "elrp.mm"
include "mpbir.mm"
include "rpexpcl.mm"
include "mp2an.mm"
include "rpcn.mm"
include "mulcli.mm"
include "10nn0.mm"
include "nn0cni.mm"
include "divcan1zi.mm"
include "div23.mm"
include "mp3an.mm"
include "oveq1i.mm"
include "eqtr3i.mm"
include "divcli.mm"
include "mulassi.mm"
include "caddc.mm"
include "expp1z.mm"
include "oveq2i.mm"
include "3eqtri.mm"
include "dpval3rp.mm"
include "0nn0.mm"
include "dp20h.mm"
include "eqtri.mm"
include "3eqtr4i.mm"

theorem dpexpp1
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  assume dpexpp1.a: |- A e. NN0
  assume dpexpp1.b: |- B e. RR+
  assume dpexpp1.1: |- ( P + 1 ) = Q
  assume dpexpp1.p: |- P e. ZZ
  assume dpexpp1.q: |- Q e. ZZ


  assert |- ( ( A . B ) x. ( ; 1 0 ^ P ) ) = ( ( 0 . _ A B ) x. ( ; 1 0 ^ Q ) )

  proof
    cA
    cB
    cdp2
    #
    c1
    cc0
    cdc
    #
    cP
    cexp
    co
    #
    cmul
    co
    #
    @0
    @1
    cdiv
    co
    #
    @1
    cQ
    cexp
    co
    #
    cmul
    co
    #
    cA
    cB
    cdp
    co
    #
    @2
    cmul
    co
    cc0
    @0
    cdp
    co
    #
    @5
    cmul
    co
    @3
    @4
    @2
    cmul
    co
    #
    @1
    cmul
    co
    #
    @4
    @2
    @1
    cmul
    co
    #
    cmul
    co
    @6
    @3
    @1
    cdiv
    co
    #
    @1
    cmul
    co
    #
    @3
    @10
    @1
    cc0
    wne
    #
    @13
    @3
    wceq
    cc0
    @1
    0re
    10pos
    gtneii
    #
    @3
    @1
    @0
    @2
    @0
    @0
    crp
    wcel
    @0
    cr
    wcel
    cA
    cB
    dpexpp1.a
    dpexpp1.b
    rpdp2cl
    #
    @0
    rpre
    ax-mp
    recni
    #
    @2
    crp
    wcel
    #
    @2
    cc
    wcel
    #
    @1
    crp
    wcel
    #
    cP
    cz
    wcel
    #
    @18
    @20
    @1
    cr
    wcel
    #
    cc0
    @1
    clt
    wbr
    #
    wa
    @22
    @23
    10re
    10pos
    pm3.2i
    @1
    elrp
    mpbir
    dpexpp1.p
    @1
    cP
    rpexpcl
    mp2an
    @2
    rpcn
    ax-mp
    #
    mulcli
    @1
    10nn0
    nn0cni
    #
    divcan1zi
    ax-mp
    @12
    @9
    @1
    cmul
    @0
    cc
    wcel
    @19
    @1
    cc
    wcel
    #
    @14
    wa
    @12
    @9
    wceq
    @17
    @24
    @26
    @14
    @25
    @15
    pm3.2i
    @0
    @2
    @1
    div23
    mp3an
    oveq1i
    eqtr3i
    @4
    @2
    @1
    @0
    @1
    @17
    @25
    @15
    divcli
    @24
    @25
    mulassi
    @11
    @5
    @4
    cmul
    @1
    cP
    c1
    caddc
    co
    #
    cexp
    co
    #
    @11
    @5
    @26
    @14
    @21
    @28
    @11
    wceq
    @25
    @15
    dpexpp1.p
    @1
    cP
    expp1z
    mp3an
    @27
    cQ
    @1
    cexp
    dpexpp1.1
    oveq2i
    eqtr3i
    oveq2i
    3eqtri
    @7
    @0
    @2
    cmul
    cA
    cB
    dpexpp1.a
    dpexpp1.b
    dpval3rp
    oveq1i
    @8
    @4
    @5
    cmul
    @8
    cc0
    @0
    cdp2
    @4
    cc0
    @0
    0nn0
    @16
    dpval3rp
    @0
    @16
    dp20h
    eqtri
    oveq1i
    3eqtr4i
end
