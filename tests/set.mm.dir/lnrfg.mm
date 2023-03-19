include "clfig.mm"
include "wcel.mm"
include "clnr.mm"
include "wa.mm"
include "cv.mm"
include "cfn.mm"
include "clspn.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "clnm.mm"
include "cpw.mm"
include "cfrlm.mm"
include "co.mm"
include "cid.mm"
include "cres.mm"
include "cvsca.mm"
include "cof.mm"
include "cgsu.mm"
include "cmpt.mm"
include "clmhm.mm"
include "crn.mm"
include "cvv.mm"
include "eqid.mm"
include "clmod.mm"
include "fglmod.mm"
include "ad3antrrr.mm"
include "vex.mm"
include "a1i.mm"
include "csca.mm"
include "wf.mm"
include "wss.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "ax-mp.mm"
include "elpwi.mm"
include "fss.mm"
include "sylancr.mm"
include "ad2antlr.mm"
include "frlmup1.mm"
include "simpllr.mm"
include "simprl.mm"
include "lnrfrlm.mm"
include "syl2anc.mm"
include "frlmup3.mm"
include "rnresi.mm"
include "fveq2i.mm"
include "simprr.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "lnmepi.mm"
include "syl3anc.mm"
include "wrex.mm"
include "wb.mm"
include "islmodfg.mm"
include "syl.mm"
include "ibi.mm"
include "adantr.mm"
include "r19.29a.mm"

theorem lnrfg
  let cS: class S
  let cM: class M
  let va: setvar a
  let vb: setvar b
  assume lnrfg.s: |- S = ( Scalar ` M )


  assert |- ( ( M e. LFinGen /\ S e. LNoeR ) -> M e. LNoeM )

  proof
    cM
    clfig
    wcel
    #
    cS
    clnr
    wcel
    #
    wa
    #
    va
    cv
    #
    cfn
    wcel
    #
    @3
    cM
    clspn
    cfv
    #
    cfv
    #
    cM
    cbs
    cfv
    #
    wceq
    #
    wa
    #
    cM
    clnm
    wcel
    #
    va
    @7
    cpw
    #
    @2
    @3
    @11
    wcel
    #
    wa
    #
    @9
    wa
    #
    vb
    cS
    @3
    cfrlm
    co
    #
    cbs
    cfv
    #
    cM
    vb
    cv
    cid
    @3
    cres
    #
    cM
    cvsca
    cfv
    #
    cof
    co
    cgsu
    co
    cmpt
    #
    @15
    cM
    clmhm
    co
    wcel
    @15
    clnm
    wcel
    #
    @19
    crn
    #
    @7
    wceq
    @10
    @14
    vb
    @17
    @16
    @7
    cS
    cM
    @18
    @19
    @15
    @3
    cvv
    @15
    eqid
    #
    @16
    eqid
    #
    @7
    eqid
    #
    @18
    eqid
    #
    @19
    eqid
    #
    @0
    cM
    clmod
    wcel
    #
    @1
    @12
    @9
    cM
    fglmod
    #
    ad3antrrr
    #
    @3
    cvv
    wcel
    @14
    va
    vex
    a1i
    #
    cS
    cM
    csca
    cfv
    wceq
    @14
    lnrfg.s
    a1i
    #
    @12
    @3
    @7
    @17
    wf
    #
    @2
    @9
    @12
    @3
    @3
    @17
    wf
    #
    @3
    @7
    wss
    @32
    @3
    @3
    @17
    wf1o
    @33
    @3
    f1oi
    @3
    @3
    @17
    f1of
    ax-mp
    @3
    @7
    elpwi
    @3
    @3
    @7
    @17
    fss
    sylancr
    ad2antlr
    #
    frlmup1
    @14
    @1
    @4
    @20
    @0
    @1
    @12
    @9
    simpllr
    @13
    @4
    @8
    simprl
    cS
    @3
    @15
    @22
    lnrfrlm
    syl2anc
    @14
    @21
    @17
    crn
    #
    @5
    cfv
    #
    @7
    @14
    vb
    @17
    @16
    @7
    cS
    cM
    @18
    @19
    @15
    @3
    @5
    cvv
    @22
    @23
    @24
    @25
    @26
    @29
    @30
    @31
    @34
    @5
    eqid
    #
    frlmup3
    @14
    @36
    @6
    @7
    @35
    @3
    @5
    @3
    rnresi
    fveq2i
    @13
    @4
    @8
    simprr
    syl5eq
    eqtrd
    @7
    @15
    cM
    @19
    @24
    lnmepi
    syl3anc
    @0
    @9
    va
    @11
    wrex
    #
    @1
    @0
    @38
    @0
    @27
    @0
    @38
    wb
    @28
    @7
    @5
    cM
    va
    @24
    @37
    islmodfg
    syl
    ibi
    adantr
    r19.29a
end
