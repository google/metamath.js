include "wcel.mm"
include "wse.mm"
include "wa.mm"
include "ctrpred.mm"
include "cpred.mm"
include "cv.mm"
include "ciun.mm"
include "cun.mm"
include "wss.mm"
include "wral.mm"
include "wo.mm"
include "elun.mm"
include "predel.mm"
include "wi.mm"
include "cvv.mm"
include "setlikespec.mm"
include "trpredpred.mm"
include "syl.mm"
include "expcom.mm"
include "adantl.mm"
include "syl5.mm"
include "ancld.mm"
include "wrex.mm"
include "weq.mm"
include "trpredeq3.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "ssiun.mm"
include "syl6.mm"
include "eliun.mm"
include "ancoms.mm"
include "adantll.mm"
include "trpredss.mm"
include "sseld.mm"
include "ad2antlr.mm"
include "syld.mm"
include "imp.mm"
include "simpr.mm"
include "simplr.mm"
include "trpredelss.mm"
include "syl2anc.mm"
include "sstrd.mm"
include "exp31.mm"
include "reximdvai.mm"
include "syl5bi.mm"
include "jaod.mm"
include "ssun4.mm"
include "ralrimiv.mm"
include "ssun1.mm"
include "jctir.mm"
include "trpredmintr.mm"
include "mpdan.mm"
include "iunss.mm"
include "sylibr.mm"
include "unssd.mm"
include "eqssd.mm"

theorem dftrpred3g
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cX: class X
  let vz: setvar z

  disjoint A y
  disjoint R y
  disjoint X y
  disjoint A z
  disjoint y z
  disjoint R z
  disjoint X z
  assert |- ( ( X e. A /\ R Se A ) -> TrPred ( R , A , X ) = ( Pred ( R , A , X ) u. U_ y e. Pred ( R , A , X ) TrPred ( R , A , y ) ) )

  proof
    cX
    cA
    wcel
    #
    cA
    cR
    wse
    #
    wa
    #
    cA
    cR
    cX
    ctrpred
    #
    cA
    cR
    cX
    cpred
    #
    vy
    @4
    cA
    cR
    vy
    cv
    #
    ctrpred
    #
    ciun
    #
    cun
    #
    @2
    cA
    cR
    vz
    cv
    #
    cpred
    #
    @8
    wss
    #
    vz
    @8
    wral
    #
    @4
    @8
    wss
    #
    wa
    @3
    @8
    wss
    @2
    @12
    @13
    @2
    @11
    vz
    @8
    @9
    @8
    wcel
    @9
    @4
    wcel
    #
    @9
    @7
    wcel
    #
    wo
    #
    @2
    @11
    @9
    @4
    @7
    elun
    @2
    @16
    @10
    @7
    wss
    #
    @11
    @2
    @14
    @17
    @15
    @2
    @14
    @14
    @10
    cA
    cR
    @9
    ctrpred
    #
    wss
    #
    wa
    #
    @17
    @2
    @14
    @19
    @14
    @9
    cA
    wcel
    #
    @2
    @19
    cA
    cR
    cX
    @9
    predel
    @1
    @21
    @19
    wi
    @0
    @21
    @1
    @19
    @21
    @1
    wa
    @10
    cvv
    wcel
    #
    @19
    cA
    cR
    @9
    setlikespec
    #
    cA
    cvv
    cR
    @9
    trpredpred
    #
    syl
    expcom
    adantl
    syl5
    ancld
    @20
    @10
    @6
    wss
    #
    vy
    @4
    wrex
    #
    @17
    @25
    @19
    vy
    @9
    @4
    vy
    vz
    weq
    @6
    @18
    @10
    cA
    cR
    @5
    @9
    trpredeq3
    sseq2d
    rspcev
    vy
    @4
    @6
    @10
    ssiun
    #
    syl
    syl6
    @15
    @9
    @6
    wcel
    #
    vy
    @4
    wrex
    #
    @2
    @17
    vy
    @9
    @4
    @6
    eliun
    @2
    @29
    @26
    @17
    @2
    @28
    @25
    vy
    @4
    @5
    @4
    wcel
    #
    @5
    cA
    wcel
    #
    @2
    @28
    @25
    wi
    cA
    cR
    cX
    @5
    predel
    @2
    @31
    @28
    @25
    @2
    @31
    wa
    #
    @28
    wa
    #
    @10
    @18
    @6
    @33
    @22
    @19
    @32
    @28
    @22
    @32
    @28
    @21
    @22
    @32
    @6
    cA
    @9
    @32
    cA
    cR
    @5
    cpred
    cvv
    wcel
    #
    @6
    cA
    wss
    @1
    @31
    @34
    @0
    @31
    @1
    @34
    cA
    cR
    @5
    setlikespec
    ancoms
    adantll
    cA
    cvv
    cR
    @5
    trpredss
    syl
    sseld
    @1
    @21
    @22
    wi
    @0
    @31
    @21
    @1
    @22
    @23
    expcom
    ad2antlr
    syld
    imp
    @24
    syl
    @32
    @28
    @18
    @6
    wss
    #
    @32
    @31
    @1
    @28
    @35
    wi
    @2
    @31
    simpr
    @0
    @1
    @31
    simplr
    cA
    cR
    @5
    @9
    trpredelss
    syl2anc
    imp
    sstrd
    exp31
    syl5
    reximdvai
    @27
    syl6
    syl5bi
    jaod
    @10
    @7
    @4
    ssun4
    syl6
    syl5bi
    ralrimiv
    @4
    @7
    ssun1
    jctir
    vz
    cA
    @8
    cR
    cX
    trpredmintr
    mpdan
    @2
    @4
    @7
    @3
    @2
    @4
    cvv
    wcel
    @4
    @3
    wss
    cA
    cR
    cX
    setlikespec
    cA
    cvv
    cR
    cX
    trpredpred
    syl
    #
    @2
    @6
    @3
    wss
    #
    vy
    @4
    wral
    @7
    @3
    wss
    @2
    @37
    vy
    @4
    @2
    @30
    @5
    @3
    wcel
    @37
    @2
    @4
    @3
    @5
    @36
    sseld
    cA
    cR
    cX
    @5
    trpredelss
    syld
    ralrimiv
    vy
    @4
    @6
    @3
    iunss
    sylibr
    unssd
    eqssd
end
