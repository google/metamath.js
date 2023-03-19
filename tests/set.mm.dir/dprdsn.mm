include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wa.mm"
include "cop.mm"
include "csn.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "cmrc.mm"
include "cvv.mm"
include "c0g.mm"
include "ccntz.mm"
include "eqid.mm"
include "cgrp.mm"
include "subgrcl.mm"
include "adantl.mm"
include "snex.mm"
include "a1i.mm"
include "wf1o.mm"
include "wf.mm"
include "f1osng.mm"
include "f1of.mm"
include "syl.mm"
include "simpr.mm"
include "snssd.mm"
include "fssd.mm"
include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "wss.mm"
include "simpr1.mm"
include "elsni.mm"
include "simpr2.mm"
include "eqtr4d.mm"
include "simpr3.mm"
include "pm2.21ddne.mm"
include "cdif.mm"
include "cima.mm"
include "cuni.mm"
include "cin.mm"
include "cbs.mm"
include "cmre.mm"
include "cacs.mm"
include "adantr.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "c0.mm"
include "sneqd.mm"
include "difeq2d.mm"
include "difid.mm"
include "syl6eq.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "unieqd.mm"
include "uni0.mm"
include "0ss.mm"
include "eqsstrd.mm"
include "0subg.mm"
include "mrcsscl.mm"
include "syl3anc.mm"
include "subg0cl.mm"
include "ad2antlr.mm"
include "fveq2d.mm"
include "fvsng.mm"
include "sylan9eqr.mm"
include "eleqtrrd.mm"
include "sstrd.mm"
include "sseqin2.mm"
include "sylib.mm"
include "dmdprdd.mm"
include "crn.mm"
include "dprdspan.mm"
include "rnsnopg.mm"
include "unisng.mm"
include "eqtrd.mm"
include "mrcid.mm"
include "sylancom.mm"
include "jca.mm"

theorem dprdsn
  let cA: class A
  let cS: class S
  let cG: class G
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ S e. ( SubGrp ` G ) ) -> ( G dom DProd { <. A , S >. } /\ ( G DProd { <. A , S >. } ) = S ) )

  proof
    cA
    cV
    wcel
    #
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    wa
    #
    cG
    cA
    cS
    cop
    csn
    #
    cdprd
    cdm
    wbr
    #
    cG
    @4
    cdprd
    co
    #
    cS
    wceq
    @3
    vx
    vy
    @4
    cG
    cA
    csn
    #
    @1
    cmrc
    cfv
    #
    cvv
    cG
    c0g
    cfv
    #
    cG
    ccntz
    cfv
    #
    @10
    eqid
    @9
    eqid
    #
    @8
    eqid
    #
    @2
    cG
    cgrp
    wcel
    #
    @0
    cS
    cG
    subgrcl
    adantl
    #
    @7
    cvv
    wcel
    @3
    cA
    snex
    a1i
    @3
    @7
    cS
    csn
    #
    @1
    @4
    @3
    @7
    @15
    @4
    wf1o
    @7
    @15
    @4
    wf
    cA
    cS
    cV
    @1
    f1osng
    @7
    @15
    @4
    f1of
    syl
    @3
    cS
    @1
    @0
    @2
    simpr
    snssd
    fssd
    @3
    vx
    cv
    #
    @7
    wcel
    #
    vy
    cv
    #
    @7
    wcel
    #
    @16
    @18
    wne
    #
    w3a
    wa
    #
    @16
    @4
    cfv
    #
    @18
    @4
    cfv
    @10
    cfv
    wss
    @16
    @18
    @21
    @16
    cA
    @18
    @21
    @17
    @16
    cA
    wceq
    #
    @3
    @17
    @19
    @20
    simpr1
    @16
    cA
    elsni
    #
    syl
    @21
    @19
    @18
    cA
    wceq
    @3
    @17
    @19
    @20
    simpr2
    @18
    cA
    elsni
    syl
    eqtr4d
    @3
    @17
    @19
    @20
    simpr3
    pm2.21ddne
    @3
    @17
    wa
    #
    @22
    @4
    @7
    @16
    csn
    #
    cdif
    #
    cima
    #
    cuni
    #
    @8
    cfv
    #
    cin
    #
    @30
    @9
    csn
    #
    @25
    @30
    @22
    wss
    @31
    @30
    wceq
    @25
    @30
    @32
    @22
    @25
    @1
    cG
    cbs
    cfv
    #
    cmre
    cfv
    wcel
    #
    @29
    @32
    wss
    @32
    @1
    wcel
    #
    @30
    @32
    wss
    @25
    @13
    @1
    @33
    cacs
    cfv
    wcel
    #
    @34
    @3
    @13
    @17
    @14
    adantr
    #
    @33
    cG
    @33
    eqid
    subgacs
    #
    @1
    @33
    acsmre
    #
    3syl
    @25
    @29
    c0
    @32
    @25
    @29
    c0
    cuni
    c0
    @25
    @28
    c0
    @25
    @28
    @4
    c0
    cima
    c0
    @25
    @27
    c0
    @4
    @25
    @27
    @7
    @7
    cdif
    c0
    @25
    @26
    @7
    @7
    @25
    @16
    cA
    @17
    @23
    @3
    @24
    adantl
    sneqd
    difeq2d
    @7
    difid
    syl6eq
    imaeq2d
    @4
    ima0
    syl6eq
    unieqd
    uni0
    syl6eq
    c0
    @32
    wss
    @25
    @32
    0ss
    a1i
    eqsstrd
    @25
    @13
    @35
    @37
    cG
    @9
    @11
    0subg
    syl
    @1
    @29
    @8
    @32
    @33
    @12
    mrcsscl
    syl3anc
    #
    @25
    @9
    @22
    @25
    @9
    cS
    @22
    @2
    @9
    cS
    wcel
    @0
    @17
    cS
    cG
    @9
    @11
    subg0cl
    ad2antlr
    @17
    @3
    @22
    cA
    @4
    cfv
    cS
    @17
    @16
    cA
    @4
    @24
    fveq2d
    cA
    cS
    cV
    @1
    fvsng
    sylan9eqr
    eleqtrrd
    snssd
    sstrd
    @30
    @22
    sseqin2
    sylib
    @40
    eqsstrd
    dmdprdd
    #
    @3
    @6
    @4
    crn
    #
    cuni
    #
    @8
    cfv
    #
    cS
    @3
    @5
    @6
    @44
    wceq
    @41
    @4
    cG
    @8
    @12
    dprdspan
    syl
    @3
    @44
    cS
    @8
    cfv
    #
    cS
    @3
    @43
    cS
    @8
    @3
    @43
    @15
    cuni
    #
    cS
    @3
    @42
    @15
    @0
    @42
    @15
    wceq
    @2
    cA
    cS
    cV
    rnsnopg
    adantr
    unieqd
    @2
    @46
    cS
    wceq
    @0
    cS
    @1
    unisng
    adantl
    eqtrd
    fveq2d
    @0
    @2
    @34
    @45
    cS
    wceq
    @3
    @13
    @36
    @34
    @14
    @38
    @39
    3syl
    @1
    cS
    @8
    @33
    @12
    mrcid
    sylancom
    eqtrd
    eqtrd
    jca
end
