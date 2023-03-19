include "wf1o.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "wss.mm"
include "wxo.mm"
include "ccom.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "excxor.mm"
include "ccnv.mm"
include "wceq.mm"
include "coass.mm"
include "cres.mm"
include "f1ococnv1.mm"
include "coeq1d.mm"
include "wf.mm"
include "f1of.mm"
include "fcoi2.mm"
include "syl.mm"
include "sylan9eq.mm"
include "syl5eqr.mm"
include "difeq1d.mm"
include "dmeqd.mm"
include "adantr.mm"
include "cun.mm"
include "mvdco.mm"
include "f1omvdcnv.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "eqsstrd.mm"
include "simprr.mm"
include "unssd.mm"
include "syl5ss.mm"
include "eqsstr3d.mm"
include "expr.mm"
include "con3d.mm"
include "expimpd.mm"
include "f1ococnv2.mm"
include "coeq2d.mm"
include "fcoi1.mm"
include "sylan9eqr.mm"
include "syl5eq.mm"
include "ad2antlr.mm"
include "ancomsd.mm"
include "jaod.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem f1omvdco2
  let cA: class A
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F : A -1-1-onto-> A /\ G : A -1-1-onto-> A /\ ( dom ( F \ _I ) C_ X \/_ dom ( G \ _I ) C_ X ) ) -> -. dom ( ( F o. G ) \ _I ) C_ X )

  proof
    cA
    cA
    cF
    wf1o
    #
    cA
    cA
    cG
    wf1o
    #
    cF
    cid
    cdif
    #
    cdm
    #
    cX
    wss
    #
    cG
    cid
    cdif
    #
    cdm
    #
    cX
    wss
    #
    wxo
    #
    cF
    cG
    ccom
    #
    cid
    cdif
    cdm
    #
    cX
    wss
    #
    wn
    #
    @8
    @4
    @7
    wn
    #
    wa
    #
    @4
    wn
    #
    @7
    wa
    #
    wo
    @0
    @1
    wa
    #
    @12
    @4
    @7
    excxor
    @17
    @14
    @12
    @16
    @17
    @4
    @13
    @12
    @17
    @4
    wa
    @11
    @7
    @17
    @4
    @11
    @7
    @17
    @4
    @11
    wa
    #
    wa
    #
    @6
    cF
    ccnv
    #
    @9
    ccom
    #
    cid
    cdif
    #
    cdm
    #
    cX
    @17
    @23
    @6
    wceq
    @18
    @17
    @22
    @5
    @17
    @21
    cG
    cid
    @17
    @21
    @20
    cF
    ccom
    #
    cG
    ccom
    #
    cG
    @20
    cF
    cG
    coass
    @0
    @1
    @25
    cid
    cA
    cres
    #
    cG
    ccom
    #
    cG
    @0
    @24
    @26
    cG
    cA
    cA
    cF
    f1ococnv1
    coeq1d
    @1
    cA
    cA
    cG
    wf
    @27
    cG
    wceq
    cA
    cA
    cG
    f1of
    cA
    cA
    cG
    fcoi2
    syl
    sylan9eq
    syl5eqr
    difeq1d
    dmeqd
    adantr
    @19
    @23
    @20
    cid
    cdif
    cdm
    #
    @10
    cun
    cX
    @20
    @9
    mvdco
    @19
    @28
    @10
    cX
    @19
    @28
    @3
    cX
    @0
    @28
    @3
    wceq
    @1
    @18
    cA
    cF
    f1omvdcnv
    ad2antrr
    @17
    @4
    @11
    simprl
    eqsstrd
    @17
    @4
    @11
    simprr
    unssd
    syl5ss
    eqsstr3d
    expr
    con3d
    expimpd
    @17
    @7
    @15
    @12
    @17
    @7
    @15
    @12
    @17
    @7
    wa
    @11
    @4
    @17
    @7
    @11
    @4
    @17
    @7
    @11
    wa
    #
    wa
    #
    @3
    @9
    cG
    ccnv
    #
    ccom
    #
    cid
    cdif
    #
    cdm
    #
    cX
    @17
    @34
    @3
    wceq
    @29
    @17
    @33
    @2
    @17
    @32
    cF
    cid
    @17
    @32
    cF
    cG
    @31
    ccom
    #
    ccom
    #
    cF
    cF
    cG
    @31
    coass
    @1
    @0
    @36
    cF
    @26
    ccom
    #
    cF
    @1
    @35
    @26
    cF
    cA
    cA
    cG
    f1ococnv2
    coeq2d
    @0
    cA
    cA
    cF
    wf
    @37
    cF
    wceq
    cA
    cA
    cF
    f1of
    cA
    cA
    cF
    fcoi1
    syl
    sylan9eqr
    syl5eq
    difeq1d
    dmeqd
    adantr
    @30
    @34
    @10
    @31
    cid
    cdif
    cdm
    #
    cun
    cX
    @9
    @31
    mvdco
    @30
    @10
    @38
    cX
    @17
    @7
    @11
    simprr
    @30
    @38
    @6
    cX
    @1
    @38
    @6
    wceq
    @0
    @29
    cA
    cG
    f1omvdcnv
    ad2antlr
    @17
    @7
    @11
    simprl
    eqsstrd
    unssd
    syl5ss
    eqsstr3d
    expr
    con3d
    expimpd
    ancomsd
    jaod
    syl5bi
    3impia
end
