include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "wa.mm"
include "cle.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wceq.mm"
include "wo.mm"
include "cfa.mm"
include "cfv.mm"
include "caddc.mm"
include "cn0.mm"
include "nnnn0.mm"
include "faccl.mm"
include "syl.mm"
include "peano2nnd.mm"
include "syl5eqel.mm"
include "nnge1d.mm"
include "wb.mm"
include "1nn.mm"
include "nnleltp1.mm"
include "sylancr.mm"
include "mpbid.mm"
include "syl6breqr.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "divid.mm"
include "3syl.mm"
include "syl6eqel.mm"
include "breq2.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "nnwos.mm"
include "infpnlem1.mm"
include "reximdva.mm"
include "mpd.mm"

theorem infpnlem2
  let vj: setvar j
  let vk: setvar k
  let cK: class K
  let cN: class N
  let cM: class M
  assume infpnlem.1: |- K = ( ( ! ` N ) + 1 )

  disjoint j k
  disjoint N j
  disjoint N k
  disjoint K j
  disjoint K k
  disjoint M j
  assert |- ( N e. NN -> E. j e. NN ( N < j /\ A. k e. NN ( ( j / k ) e. NN -> ( k = 1 \/ k = j ) ) ) )

  proof
    cN
    cn
    wcel
    #
    c1
    vj
    cv
    #
    clt
    wbr
    #
    cK
    @1
    cdiv
    co
    #
    cn
    wcel
    #
    wa
    #
    c1
    vk
    cv
    #
    clt
    wbr
    #
    cK
    @6
    cdiv
    co
    #
    cn
    wcel
    #
    wa
    #
    @1
    @6
    cle
    wbr
    wi
    vk
    cn
    wral
    wa
    #
    vj
    cn
    wrex
    #
    cN
    @1
    clt
    wbr
    @1
    @6
    cdiv
    co
    cn
    wcel
    @6
    c1
    wceq
    @6
    @1
    wceq
    wo
    wi
    vk
    cn
    wral
    wa
    #
    vj
    cn
    wrex
    @0
    @5
    vj
    cn
    wrex
    #
    @12
    @0
    cK
    cn
    wcel
    #
    c1
    cK
    clt
    wbr
    #
    cK
    cK
    cdiv
    co
    #
    cn
    wcel
    #
    @14
    @0
    cK
    cN
    cfa
    cfv
    #
    c1
    caddc
    co
    #
    cn
    infpnlem.1
    @0
    @19
    @0
    cN
    cn0
    wcel
    @19
    cn
    wcel
    #
    cN
    nnnn0
    cN
    faccl
    syl
    #
    peano2nnd
    syl5eqel
    #
    @0
    c1
    @20
    cK
    clt
    @0
    c1
    @19
    cle
    wbr
    #
    c1
    @20
    clt
    wbr
    #
    @0
    @19
    @22
    nnge1d
    @0
    c1
    cn
    wcel
    @21
    @24
    @25
    wb
    1nn
    @22
    c1
    @19
    nnleltp1
    sylancr
    mpbid
    infpnlem.1
    syl6breqr
    @0
    @17
    c1
    cn
    @0
    @15
    cK
    cc
    wcel
    #
    cK
    cc0
    wne
    #
    wa
    @17
    c1
    wceq
    @23
    @15
    @26
    @27
    cK
    nncn
    cK
    nnne0
    jca
    cK
    divid
    3syl
    1nn
    syl6eqel
    @5
    @16
    @18
    wa
    vj
    cK
    cn
    @1
    cK
    wceq
    #
    @2
    @16
    @4
    @18
    @1
    cK
    c1
    clt
    breq2
    @28
    @3
    @17
    cn
    @1
    cK
    cK
    cdiv
    oveq2
    eleq1d
    anbi12d
    rspcev
    syl12anc
    @5
    @10
    vj
    vk
    @1
    @6
    wceq
    #
    @2
    @7
    @4
    @9
    @1
    @6
    c1
    clt
    breq2
    @29
    @3
    @8
    cn
    @1
    @6
    cK
    cdiv
    oveq2
    eleq1d
    anbi12d
    nnwos
    syl
    @0
    @11
    @13
    vj
    cn
    vk
    cK
    @1
    cN
    infpnlem.1
    infpnlem1
    reximdva
    mpd
end
