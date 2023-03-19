include "cq.mm"
include "wcel.mm"
include "cn.mm"
include "cexp.mm"
include "co.mm"
include "cz.mm"
include "w3a.mm"
include "cc0.mm"
include "eleq1.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cpc.mm"
include "cle.mm"
include "wbr.mm"
include "cprime.mm"
include "wral.mm"
include "cmul.mm"
include "simpll2.mm"
include "nncnd.mm"
include "mul01d.mm"
include "cn0.mm"
include "simpr.mm"
include "simpll3.mm"
include "cc.mm"
include "simpll1.mm"
include "qcn.mm"
include "syl.mm"
include "simplr.mm"
include "nnzd.mm"
include "expne0d.mm"
include "pczcl.mm"
include "syl12anc.mm"
include "nn0ge0d.mm"
include "wceq.mm"
include "pcexp.mm"
include "syl121anc.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "cr.mm"
include "clt.mm"
include "wb.mm"
include "0red.mm"
include "pcqcl.mm"
include "zred.mm"
include "nnred.mm"
include "nngt0d.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "simpl1.mm"
include "pcz.mm"
include "0zd.mm"
include "pm2.61ne.mm"

theorem qexpz
  let cA: class A
  let cN: class N
  let vp: setvar p


  assert |- ( ( A e. QQ /\ N e. NN /\ ( A ^ N ) e. ZZ ) -> A e. ZZ )

  proof
    cA
    cq
    wcel
    #
    cN
    cn
    wcel
    #
    cA
    cN
    cexp
    co
    #
    cz
    wcel
    #
    w3a
    #
    cA
    cz
    wcel
    #
    cc0
    cz
    wcel
    cA
    cc0
    cA
    cc0
    cz
    eleq1
    @4
    cA
    cc0
    wne
    #
    wa
    #
    @5
    cc0
    vp
    cv
    #
    cA
    cpc
    co
    #
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    @7
    @10
    vp
    cprime
    @7
    @8
    cprime
    wcel
    #
    wa
    #
    @10
    cN
    cc0
    cmul
    co
    #
    cN
    @9
    cmul
    co
    #
    cle
    wbr
    #
    @13
    @14
    cc0
    @15
    cle
    @13
    cN
    @13
    cN
    @0
    @1
    @3
    @6
    @12
    simpll2
    #
    nncnd
    mul01d
    @13
    cc0
    @8
    @2
    cpc
    co
    #
    @15
    cle
    @13
    @18
    @13
    @12
    @3
    @2
    cc0
    wne
    @18
    cn0
    wcel
    @7
    @12
    simpr
    #
    @0
    @1
    @3
    @6
    @12
    simpll3
    @13
    cA
    cN
    @13
    @0
    cA
    cc
    wcel
    @0
    @1
    @3
    @6
    @12
    simpll1
    #
    cA
    qcn
    syl
    @4
    @6
    @12
    simplr
    #
    @13
    cN
    @17
    nnzd
    #
    expne0d
    @8
    @2
    pczcl
    syl12anc
    nn0ge0d
    @13
    @12
    @0
    @6
    cN
    cz
    wcel
    @18
    @15
    wceq
    @19
    @20
    @21
    @22
    cA
    @8
    cN
    pcexp
    syl121anc
    breqtrd
    eqbrtrd
    @13
    cc0
    cr
    wcel
    @9
    cr
    wcel
    cN
    cr
    wcel
    cc0
    cN
    clt
    wbr
    @10
    @16
    wb
    @13
    0red
    @13
    @9
    @13
    @12
    @0
    @6
    @9
    cz
    wcel
    @19
    @20
    @21
    @8
    cA
    pcqcl
    syl12anc
    zred
    @13
    cN
    @17
    nnred
    @13
    cN
    @17
    nngt0d
    cc0
    @9
    cN
    lemul2
    syl112anc
    mpbird
    ralrimiva
    @7
    @0
    @5
    @11
    wb
    @0
    @1
    @3
    @6
    simpl1
    cA
    vp
    pcz
    syl
    mpbird
    @4
    0zd
    pm2.61ne
end
