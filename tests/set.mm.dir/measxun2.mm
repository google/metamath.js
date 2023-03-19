include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "w3a.mm"
include "cdif.mm"
include "cpr.mm"
include "cuni.mm"
include "cv.mm"
include "cesum.mm"
include "cxad.mm"
include "co.mm"
include "cpw.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2r.mm"
include "csiga.mm"
include "crn.mm"
include "measbase.mm"
include "syl.mm"
include "simp2l.mm"
include "difelsiga.mm"
include "syl3anc.mm"
include "prelpwi.mm"
include "syl2anc.mm"
include "prct.mm"
include "simp3.mm"
include "cin.mm"
include "disjdifprg2.mm"
include "prcom.mm"
include "dfss.mm"
include "biimpi.mm"
include "incom.mm"
include "syl6eq.mm"
include "preq2d.mm"
include "syl5eqr.mm"
include "disjeq1d.mm"
include "biimprd.mm"
include "mpan9.mm"
include "jca.mm"
include "measvun.mm"
include "cun.mm"
include "uniprg.mm"
include "undif.mm"
include "sylan9eq.mm"
include "fveq2d.mm"
include "simpr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "measvxrge0.mm"
include "wo.mm"
include "c0.mm"
include "eqimss.mm"
include "ssdifeq0.mm"
include "sylib.mm"
include "measvnul.mm"
include "sylan9eqr.mm"
include "sylan.mm"
include "orcd.mm"
include "ex.mm"
include "esumpr2.mm"
include "3eqtr3d.mm"

theorem measxun2
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let vx: setvar x


  assert |- ( ( M e. ( measures ` S ) /\ ( A e. S /\ B e. S ) /\ B C_ A ) -> ( M ` A ) = ( ( M ` B ) +e ( M ` ( A \ B ) ) ) )

  proof
    cM
    cS
    cmeas
    cfv
    wcel
    #
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    wa
    #
    cB
    cA
    wss
    #
    w3a
    #
    cB
    cA
    cB
    cdif
    #
    cpr
    #
    cuni
    #
    cM
    cfv
    #
    @7
    vx
    cv
    #
    cM
    cfv
    #
    vx
    cesum
    #
    cA
    cM
    cfv
    #
    cB
    cM
    cfv
    #
    @6
    cM
    cfv
    #
    cxad
    co
    @5
    @0
    @7
    cS
    cpw
    wcel
    #
    @7
    com
    cdom
    wbr
    #
    vx
    @7
    @10
    wdisj
    #
    wa
    @9
    @12
    wceq
    @0
    @3
    @4
    simp1
    #
    @5
    @2
    @6
    cS
    wcel
    #
    @16
    @0
    @1
    @2
    @4
    simp2r
    #
    @5
    cS
    csiga
    crn
    cuni
    wcel
    #
    @1
    @2
    @20
    @5
    @0
    @22
    @19
    cS
    cM
    measbase
    syl
    @0
    @1
    @2
    @4
    simp2l
    #
    @21
    cA
    cB
    cS
    difelsiga
    syl3anc
    #
    cB
    @6
    cS
    prelpwi
    syl2anc
    @5
    @17
    @18
    @5
    @2
    @20
    @17
    @21
    @24
    cB
    @6
    cS
    cS
    prct
    syl2anc
    @5
    @1
    @4
    @18
    @23
    @0
    @3
    @4
    simp3
    #
    @1
    vx
    @6
    cA
    cB
    cin
    #
    cpr
    #
    @10
    wdisj
    #
    @4
    @18
    vx
    cA
    cB
    cS
    disjdifprg2
    @4
    @18
    @28
    @4
    vx
    @7
    @27
    @10
    @4
    @7
    @6
    cB
    cpr
    @27
    @6
    cB
    prcom
    @4
    cB
    @26
    @6
    @4
    cB
    cB
    cA
    cin
    #
    @26
    @4
    cB
    @29
    wceq
    cB
    cA
    dfss
    biimpi
    cB
    cA
    incom
    syl6eq
    preq2d
    syl5eqr
    disjeq1d
    biimprd
    mpan9
    syl2anc
    jca
    vx
    @7
    cS
    cM
    measvun
    syl3anc
    @5
    @2
    @20
    wa
    #
    @4
    @9
    @13
    wceq
    @5
    @2
    @20
    @21
    @24
    jca
    @25
    @30
    @4
    wa
    @8
    cA
    cM
    @30
    @4
    @8
    cB
    @6
    cun
    #
    cA
    cB
    @6
    cS
    cS
    uniprg
    @4
    @31
    cA
    wceq
    cB
    cA
    undif
    biimpi
    sylan9eq
    fveq2d
    syl2anc
    @5
    cB
    @6
    @11
    @14
    vx
    @15
    cS
    cS
    @5
    @10
    cB
    wceq
    #
    wa
    @10
    cB
    cM
    @5
    @32
    simpr
    fveq2d
    @5
    @10
    @6
    wceq
    #
    wa
    @10
    @6
    cM
    @5
    @33
    simpr
    fveq2d
    @21
    @24
    @5
    @0
    @2
    @14
    cc0
    cpnf
    cicc
    co
    #
    wcel
    @19
    @21
    cB
    cS
    cM
    measvxrge0
    syl2anc
    @5
    @0
    @20
    @15
    @34
    wcel
    @19
    @24
    @6
    cS
    cM
    measvxrge0
    syl2anc
    @5
    cB
    @6
    wceq
    #
    @14
    cc0
    wceq
    #
    @14
    cpnf
    wceq
    #
    wo
    @5
    @35
    wa
    @36
    @37
    @5
    @0
    @35
    @36
    @19
    @35
    @0
    @14
    c0
    cM
    cfv
    cc0
    @35
    cB
    c0
    cM
    @35
    cB
    @6
    wss
    cB
    c0
    wceq
    cB
    @6
    eqimss
    cB
    cA
    ssdifeq0
    sylib
    fveq2d
    cS
    cM
    measvnul
    sylan9eqr
    sylan
    orcd
    ex
    esumpr2
    3eqtr3d
end
