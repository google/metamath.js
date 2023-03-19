include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cc.mm"
include "ccncf.mm"
include "co.mm"
include "wa.mm"
include "cr.mm"
include "cpm.mm"
include "cre.mm"
include "ccom.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cim.mm"
include "cioo.mm"
include "crn.mm"
include "wral.mm"
include "cmbf.mm"
include "wf.mm"
include "wss.mm"
include "cncff.mm"
include "mblss.mm"
include "cvv.mm"
include "cnex.mm"
include "reex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "syl2anr.mm"
include "ctg.mm"
include "cfv.mm"
include "crest.mm"
include "simpll.mm"
include "ccn.mm"
include "simplr.mm"
include "recncf.mm"
include "a1i.mm"
include "cncfco.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "wceq.mm"
include "ad2antrr.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "eqid.mm"
include "tgioo2.mm"
include "cncfcn.mm"
include "sylancl.mm"
include "rerest.mm"
include "syl.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "eleqtrd.mm"
include "ctb.mm"
include "retopbas.mm"
include "bastg.mm"
include "ax-mp.mm"
include "simpr.mm"
include "sseldi.mm"
include "cnima.mm"
include "syl2anc.mm"
include "subopnmbl.mm"
include "imcncf.mm"
include "jca.mm"
include "ralrimiva.mm"
include "ismbf1.mm"
include "sylanbrc.mm"

theorem cnmbf
  let cA: class A
  let cF: class F
  let vx: setvar x


  assert |- ( ( A e. dom vol /\ F e. ( A -cn-> CC ) ) -> F e. MblFn )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cF
    cA
    cc
    ccncf
    co
    wcel
    #
    wa
    #
    cF
    cc
    cr
    cpm
    co
    wcel
    #
    cre
    cF
    ccom
    #
    ccnv
    vx
    cv
    #
    cima
    #
    @0
    wcel
    #
    cim
    cF
    ccom
    #
    ccnv
    @6
    cima
    #
    @0
    wcel
    #
    wa
    #
    vx
    cioo
    crn
    #
    wral
    cF
    cmbf
    wcel
    @2
    cA
    cc
    cF
    wf
    #
    cA
    cr
    wss
    #
    @4
    @1
    cA
    cc
    cF
    cncff
    cA
    mblss
    #
    cc
    cvv
    wcel
    cr
    cvv
    wcel
    @14
    @15
    wa
    @4
    cnex
    reex
    cc
    cr
    cA
    cF
    cvv
    cvv
    elpm2r
    mpanl12
    syl2anr
    @3
    @12
    vx
    @13
    @3
    @6
    @13
    wcel
    #
    wa
    #
    @8
    @11
    @18
    @1
    @7
    @13
    ctg
    cfv
    #
    cA
    crest
    co
    #
    wcel
    #
    @8
    @1
    @2
    @17
    simpll
    #
    @18
    @5
    @20
    @19
    ccn
    co
    #
    wcel
    @6
    @19
    wcel
    #
    @21
    @18
    @5
    cA
    cr
    ccncf
    co
    #
    @23
    @18
    cA
    cc
    cr
    cF
    cre
    @1
    @2
    @17
    simplr
    #
    cre
    cc
    cr
    ccncf
    co
    #
    wcel
    @18
    recncf
    a1i
    cncfco
    @18
    @25
    ccnfld
    ctopn
    cfv
    #
    cA
    crest
    co
    #
    @19
    ccn
    co
    #
    @23
    @18
    cA
    cc
    wss
    cr
    cc
    wss
    @25
    @30
    wceq
    @18
    cA
    cr
    cc
    @1
    @15
    @2
    @17
    @16
    ad2antrr
    #
    ax-resscn
    syl6ss
    ax-resscn
    cA
    cr
    @28
    @29
    @19
    @28
    eqid
    #
    @29
    eqid
    @28
    @32
    tgioo2
    cncfcn
    sylancl
    @18
    @29
    @20
    @19
    ccn
    @18
    @15
    @29
    @20
    wceq
    @31
    cA
    @19
    @28
    @32
    @19
    eqid
    rerest
    syl
    oveq1d
    eqtrd
    #
    eleqtrd
    @18
    @13
    @19
    @6
    @13
    ctb
    wcel
    @13
    @19
    wss
    retopbas
    @13
    ctb
    bastg
    ax-mp
    @3
    @17
    simpr
    sseldi
    #
    @6
    @5
    @20
    @19
    cnima
    syl2anc
    cA
    @7
    @20
    @20
    eqid
    #
    subopnmbl
    syl2anc
    @18
    @1
    @10
    @20
    wcel
    #
    @11
    @22
    @18
    @9
    @23
    wcel
    @24
    @36
    @18
    @9
    @25
    @23
    @18
    cA
    cc
    cr
    cF
    cim
    @26
    cim
    @27
    wcel
    @18
    imcncf
    a1i
    cncfco
    @33
    eleqtrd
    @34
    @6
    @9
    @20
    @19
    cnima
    syl2anc
    cA
    @10
    @20
    @35
    subopnmbl
    syl2anc
    jca
    ralrimiva
    vx
    cF
    ismbf1
    sylanbrc
end
