include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmin.mm"
include "wi.mm"
include "cr.mm"
include "cc0.mm"
include "wb.mm"
include "nnre.mm"
include "nngt0.mm"
include "jca.mm"
include "ltdiv1.mm"
include "syl3an.mm"
include "nnsub.mm"
include "sylan9bb.mm"
include "biimpd.mm"
include "exp32.mm"
include "com34.mm"
include "imp32.mm"
include "caddc.mm"
include "nnaddcl.mm"
include "expcom.mm"
include "cc.mm"
include "wceq.mm"
include "wne.mm"
include "nnsscn.mm"
include "nnne0.mm"
include "divcl.mm"
include "nnssi2.mm"
include "anim12i.mm"
include "3impdir.mm"
include "npcan.mm"
include "ancoms.mm"
include "syl.mm"
include "eleq1d.mm"
include "sylan9r.mm"
include "adantrr.mm"
include "impbid.mm"
include "nncn.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "3ad2ant3.mm"
include "divsubdir.mm"
include "syl3anc.mm"
include "adantr.mm"
include "bitr4d.mm"

theorem nndivsub
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A / C ) e. NN /\ A < B ) ) -> ( ( B / C ) e. NN <-> ( ( B - A ) / C ) e. NN ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cC
    cn
    wcel
    #
    w3a
    #
    cA
    cC
    cdiv
    co
    #
    cn
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    wa
    #
    wa
    #
    cB
    cC
    cdiv
    co
    #
    cn
    wcel
    #
    @9
    @4
    cmin
    co
    #
    cn
    wcel
    #
    cB
    cA
    cmin
    co
    cC
    cdiv
    co
    #
    cn
    wcel
    #
    @8
    @10
    @12
    @3
    @5
    @6
    @10
    @12
    wi
    @3
    @5
    @10
    @6
    @12
    @3
    @5
    @10
    @6
    @12
    wi
    @3
    @5
    @10
    wa
    #
    wa
    @6
    @12
    @3
    @6
    @4
    @9
    clt
    wbr
    #
    @15
    @12
    @0
    cA
    cr
    wcel
    @1
    cB
    cr
    wcel
    @2
    cC
    cr
    wcel
    #
    cc0
    cC
    clt
    wbr
    #
    wa
    @6
    @16
    wb
    cA
    nnre
    cB
    nnre
    @2
    @17
    @18
    cC
    nnre
    cC
    nngt0
    jca
    cA
    cB
    cC
    ltdiv1
    syl3an
    @4
    @9
    nnsub
    sylan9bb
    biimpd
    exp32
    com34
    imp32
    @3
    @5
    @12
    @10
    wi
    @6
    @5
    @12
    @11
    @4
    caddc
    co
    #
    cn
    wcel
    #
    @3
    @10
    @12
    @5
    @20
    @11
    @4
    nnaddcl
    expcom
    @3
    @20
    @10
    @3
    @19
    @9
    cn
    @3
    @4
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    wa
    #
    @19
    @9
    wceq
    #
    @0
    @2
    @1
    @23
    @0
    @2
    wa
    @21
    @1
    @2
    wa
    @22
    cC
    cc0
    wne
    #
    @21
    cA
    cC
    cc
    nnsscn
    cC
    nnne0
    #
    cA
    cC
    divcl
    nnssi2
    @25
    @22
    cB
    cC
    cc
    nnsscn
    @26
    cB
    cC
    divcl
    nnssi2
    anim12i
    3impdir
    @22
    @21
    @24
    @9
    @4
    npcan
    ancoms
    syl
    eleq1d
    biimpd
    sylan9r
    adantrr
    impbid
    @3
    @14
    @12
    wb
    @7
    @3
    @13
    @11
    cn
    @3
    cB
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    @25
    wa
    #
    @13
    @11
    wceq
    @1
    @0
    @27
    @2
    cB
    nncn
    3ad2ant2
    @0
    @1
    @28
    @2
    cA
    nncn
    3ad2ant1
    @2
    @0
    @30
    @1
    @2
    @29
    @25
    cC
    nncn
    @26
    jca
    3ad2ant3
    cB
    cA
    cC
    divsubdir
    syl3anc
    eleq1d
    adantr
    bitr4d
end
