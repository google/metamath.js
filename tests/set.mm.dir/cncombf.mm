include "cmbf.mm"
include "wcel.mm"
include "wf.mm"
include "cc.mm"
include "ccncf.mm"
include "co.mm"
include "w3a.mm"
include "ccom.mm"
include "cr.mm"
include "cpm.mm"
include "cre.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cvol.mm"
include "cdm.mm"
include "cim.mm"
include "wa.mm"
include "cioo.mm"
include "crn.mm"
include "wral.mm"
include "wss.mm"
include "simp3.mm"
include "cncff.mm"
include "syl.mm"
include "simp2.mm"
include "fco.mm"
include "syl2anc.mm"
include "wceq.mm"
include "fdm.mm"
include "mbfdm.mm"
include "3ad2ant1.mm"
include "eqeltrrd.mm"
include "mblss.mm"
include "cvv.mm"
include "cnex.mm"
include "reex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "recncf.mm"
include "a1i.mm"
include "cncfco.mm"
include "adantr.mm"
include "cnvco.mm"
include "imaeq1i.mm"
include "imaco.mm"
include "eqtri.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "simplll.mm"
include "simpllr.mm"
include "cncfrss.mm"
include "adantl.mm"
include "ctg.mm"
include "ccn.mm"
include "simpr.mm"
include "ax-resscn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "cncfcn.mm"
include "sylancl.mm"
include "eleqtrd.mm"
include "ctb.mm"
include "retopbas.mm"
include "bastg.mm"
include "ax-mp.mm"
include "simplr.mm"
include "sseldi.mm"
include "cnima.mm"
include "mbfimaopn2.mm"
include "syl31anc.mm"
include "syl5eqel.mm"
include "ralrimiva.mm"
include "3adantl3.mm"
include "coeq1.mm"
include "coass.mm"
include "syl6eq.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "imcncf.mm"
include "jca.mm"
include "ismbf1.mm"
include "sylanbrc.mm"

theorem cncombf
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vg: setvar g
  let vx: setvar x


  assert |- ( ( F e. MblFn /\ F : A --> B /\ G e. ( B -cn-> CC ) ) -> ( G o. F ) e. MblFn )

  proof
    cF
    cmbf
    wcel
    #
    cA
    cB
    cF
    wf
    #
    cG
    cB
    cc
    ccncf
    co
    wcel
    #
    w3a
    #
    cG
    cF
    ccom
    #
    cc
    cr
    cpm
    co
    wcel
    #
    cre
    @4
    ccom
    #
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cvol
    cdm
    #
    wcel
    #
    cim
    @4
    ccom
    #
    ccnv
    #
    @8
    cima
    #
    @10
    wcel
    #
    wa
    #
    vx
    cioo
    crn
    #
    wral
    @4
    cmbf
    wcel
    @3
    cA
    cc
    @4
    wf
    #
    cA
    cr
    wss
    #
    @5
    @3
    cB
    cc
    cG
    wf
    #
    @1
    @18
    @3
    @2
    @20
    @0
    @1
    @2
    simp3
    #
    cB
    cc
    cG
    cncff
    syl
    @0
    @1
    @2
    simp2
    #
    cA
    cB
    cc
    cG
    cF
    fco
    syl2anc
    @3
    cA
    @10
    wcel
    @19
    @3
    cF
    cdm
    #
    cA
    @10
    @3
    @1
    @23
    cA
    wceq
    @22
    cA
    cB
    cF
    fdm
    syl
    @0
    @1
    @23
    @10
    wcel
    @2
    cF
    mbfdm
    3ad2ant1
    eqeltrrd
    cA
    mblss
    syl
    cc
    cvv
    wcel
    cr
    cvv
    wcel
    @18
    @19
    wa
    @5
    cnex
    reex
    cc
    cr
    cA
    @4
    cvv
    cvv
    elpm2r
    mpanl12
    syl2anc
    @3
    @16
    vx
    @17
    @3
    @8
    @17
    wcel
    #
    wa
    #
    @11
    @15
    @25
    cre
    cG
    ccom
    #
    cB
    cr
    ccncf
    co
    #
    wcel
    #
    vg
    cv
    #
    cF
    ccom
    #
    ccnv
    #
    @8
    cima
    #
    @10
    wcel
    #
    vg
    @27
    wral
    #
    @11
    @3
    @28
    @24
    @3
    cB
    cc
    cr
    cG
    cre
    @21
    cre
    cc
    cr
    ccncf
    co
    #
    wcel
    @3
    recncf
    a1i
    cncfco
    adantr
    @0
    @1
    @24
    @34
    @2
    @0
    @1
    wa
    #
    @24
    wa
    #
    @33
    vg
    @27
    @37
    @29
    @27
    wcel
    #
    wa
    #
    @32
    cF
    ccnv
    #
    @29
    ccnv
    #
    @8
    cima
    #
    cima
    #
    @10
    @32
    @40
    @41
    ccom
    #
    @8
    cima
    @43
    @31
    @44
    @8
    @29
    cF
    cnvco
    imaeq1i
    @40
    @41
    @8
    imaco
    eqtri
    @39
    @0
    @1
    cB
    cc
    wss
    #
    @42
    ccnfld
    ctopn
    cfv
    #
    cB
    crest
    co
    #
    wcel
    #
    @43
    @10
    wcel
    @0
    @1
    @24
    @38
    simplll
    @0
    @1
    @24
    @38
    simpllr
    @38
    @45
    @37
    cB
    cr
    @29
    cncfrss
    adantl
    #
    @39
    @29
    @47
    @17
    ctg
    cfv
    #
    ccn
    co
    #
    wcel
    @8
    @50
    wcel
    @48
    @39
    @29
    @27
    @51
    @37
    @38
    simpr
    @39
    @45
    cr
    cc
    wss
    @27
    @51
    wceq
    @49
    ax-resscn
    cB
    cr
    @46
    @47
    @50
    @46
    eqid
    #
    @47
    eqid
    #
    @46
    @52
    tgioo2
    cncfcn
    sylancl
    eleqtrd
    @39
    @17
    @50
    @8
    @17
    ctb
    wcel
    @17
    @50
    wss
    retopbas
    @17
    ctb
    bastg
    ax-mp
    @36
    @24
    @38
    simplr
    sseldi
    @8
    @29
    @47
    @50
    cnima
    syl2anc
    cA
    cB
    @42
    cF
    @46
    @47
    @52
    @53
    mbfimaopn2
    syl31anc
    syl5eqel
    ralrimiva
    3adantl3
    #
    @33
    @11
    vg
    @26
    @27
    @29
    @26
    wceq
    #
    @32
    @9
    @10
    @55
    @31
    @7
    @8
    @55
    @30
    @6
    @55
    @30
    @26
    cF
    ccom
    @6
    @29
    @26
    cF
    coeq1
    cre
    cG
    cF
    coass
    syl6eq
    cnveqd
    imaeq1d
    eleq1d
    rspcv
    sylc
    @25
    cim
    cG
    ccom
    #
    @27
    wcel
    #
    @34
    @15
    @3
    @57
    @24
    @3
    cB
    cc
    cr
    cG
    cim
    @21
    cim
    @35
    wcel
    @3
    imcncf
    a1i
    cncfco
    adantr
    @54
    @33
    @15
    vg
    @56
    @27
    @29
    @56
    wceq
    #
    @32
    @14
    @10
    @58
    @31
    @13
    @8
    @58
    @30
    @12
    @58
    @30
    @56
    cF
    ccom
    @12
    @29
    @56
    cF
    coeq1
    cim
    cG
    cF
    coass
    syl6eq
    cnveqd
    imaeq1d
    eleq1d
    rspcv
    sylc
    jca
    ralrimiva
    vx
    @4
    ismbf1
    sylanbrc
end
