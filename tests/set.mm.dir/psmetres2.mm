include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cxp.mm"
include "cres.mm"
include "cxr.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "psmetf.mm"
include "adantr.mm"
include "simpr.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "fssresd.mm"
include "ovresd.mm"
include "simpll.mm"
include "sselda.mm"
include "psmet0.mm"
include "eqtrd.mm"
include "ad2antrr.mm"
include "psmettri2.mm"
include "syl13anc.mm"
include "oveq12d.mm"
include "3brtr4d.mm"
include "ralrimiva.mm"
include "jca.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "ssexd.mm"
include "ispsmet.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem psmetres2
  let cD: class D
  let cR: class R
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( D e. ( PsMet ` X ) /\ R C_ X ) -> ( D |` ( R X. R ) ) e. ( PsMet ` R ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cR
    cX
    wss
    #
    wa
    #
    cD
    cR
    cR
    cxp
    #
    cres
    #
    cR
    cpsmet
    cfv
    wcel
    #
    @3
    cxr
    @4
    wf
    #
    va
    cv
    #
    @7
    @4
    co
    #
    cc0
    wceq
    #
    @7
    vb
    cv
    #
    @4
    co
    #
    vc
    cv
    #
    @7
    @4
    co
    #
    @12
    @10
    @4
    co
    #
    cxad
    co
    #
    cle
    wbr
    #
    vc
    cR
    wral
    #
    vb
    cR
    wral
    #
    wa
    #
    va
    cR
    wral
    #
    @2
    cX
    cX
    cxp
    #
    cxr
    @3
    cD
    @0
    @21
    cxr
    cD
    wf
    @1
    cD
    cX
    psmetf
    adantr
    @2
    @1
    @1
    @3
    @21
    wss
    @0
    @1
    simpr
    #
    @22
    cR
    cX
    cR
    cX
    xpss12
    syl2anc
    fssresd
    @2
    @19
    va
    cR
    @2
    @7
    cR
    wcel
    #
    wa
    #
    @9
    @18
    @24
    @8
    @7
    @7
    cD
    co
    #
    cc0
    @24
    @7
    @7
    cD
    cR
    @2
    @23
    simpr
    #
    @26
    ovresd
    @24
    @0
    @7
    cX
    wcel
    #
    @25
    cc0
    wceq
    @0
    @1
    @23
    simpll
    #
    @2
    cR
    cX
    @7
    @22
    sselda
    #
    @7
    cD
    cX
    psmet0
    syl2anc
    eqtrd
    @24
    @17
    vb
    cR
    @24
    @10
    cR
    wcel
    #
    wa
    #
    @16
    vc
    cR
    @31
    @12
    cR
    wcel
    #
    wa
    #
    @7
    @10
    cD
    co
    #
    @12
    @7
    cD
    co
    #
    @12
    @10
    cD
    co
    #
    cxad
    co
    #
    @11
    @15
    cle
    @33
    @0
    @12
    cX
    wcel
    @27
    @10
    cX
    wcel
    #
    @34
    @37
    cle
    wbr
    @24
    @0
    @30
    @32
    @28
    ad2antrr
    @31
    cR
    cX
    @12
    @2
    @1
    @23
    @30
    @22
    ad2antrr
    sselda
    @24
    @27
    @30
    @32
    @29
    ad2antrr
    @31
    @38
    @32
    @24
    cR
    cX
    @10
    @2
    @1
    @23
    @22
    adantr
    sselda
    adantr
    @7
    @10
    @12
    cD
    cX
    psmettri2
    syl13anc
    @31
    @11
    @34
    wceq
    @32
    @31
    @7
    @10
    cD
    cR
    @24
    @23
    @30
    @26
    adantr
    @24
    @30
    simpr
    #
    ovresd
    adantr
    @33
    @13
    @35
    @14
    @36
    cxad
    @33
    @12
    @7
    cD
    cR
    @31
    @32
    simpr
    #
    @24
    @23
    @30
    @32
    @26
    ad2antrr
    ovresd
    @33
    @12
    @10
    cD
    cR
    @40
    @31
    @30
    @32
    @39
    adantr
    ovresd
    oveq12d
    3brtr4d
    ralrimiva
    ralrimiva
    jca
    ralrimiva
    @2
    cR
    cvv
    wcel
    @5
    @6
    @20
    wa
    wb
    @2
    cR
    cX
    cvv
    @0
    cX
    cvv
    wcel
    @1
    cD
    cX
    cpsmet
    elfvex
    adantr
    @22
    ssexd
    va
    vb
    vc
    @4
    cvv
    cR
    ispsmet
    syl
    mpbir2and
end
