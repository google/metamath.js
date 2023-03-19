include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cplusg.mm"
include "wral.mm"
include "cminusg.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "wceq.mm"
include "eqid.mm"
include "ghmf.mm"
include "adantr.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "c0g.mm"
include "cgrp.mm"
include "ghmgrp1.mm"
include "grpidcl.mm"
include "ghmid.mm"
include "subg0cl.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "mpbir2and.mm"
include "ne0i.mm"
include "ad2antrr.mm"
include "simprll.mm"
include "simprrl.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "simpll.mm"
include "ghmlin.mm"
include "simplr.mm"
include "simprlr.mm"
include "simprrr.mm"
include "subgcl.mm"
include "expr.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "simprl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ghminv.mm"
include "ad2ant2r.mm"
include "subginvcl.mm"
include "ad2ant2l.mm"
include "jca.mm"
include "ex.mm"
include "w3a.mm"
include "issubg2.mm"
include "mpbir3and.mm"

theorem ghmpreima
  let cS: class S
  let cT: class T
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b


  assert |- ( ( F e. ( S GrpHom T ) /\ V e. ( SubGrp ` T ) ) -> ( `' F " V ) e. ( SubGrp ` S ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cV
    cT
    csubg
    cfv
    wcel
    #
    wa
    #
    cF
    ccnv
    cV
    cima
    #
    cS
    csubg
    cfv
    wcel
    #
    @3
    cS
    cbs
    cfv
    #
    wss
    #
    @3
    c0
    wne
    #
    va
    cv
    #
    vb
    cv
    #
    cS
    cplusg
    cfv
    #
    co
    #
    @3
    wcel
    #
    vb
    @3
    wral
    #
    @8
    cS
    cminusg
    cfv
    #
    cfv
    #
    @3
    wcel
    #
    wa
    #
    va
    @3
    wral
    #
    @2
    cF
    cdm
    #
    @3
    @5
    cF
    cV
    cnvimass
    @2
    @5
    cT
    cbs
    cfv
    #
    cF
    wf
    #
    @19
    @5
    wceq
    @0
    @21
    @1
    cS
    cT
    cF
    @5
    @20
    @5
    eqid
    #
    @20
    eqid
    ghmf
    adantr
    #
    @5
    @20
    cF
    fdm
    syl
    syl5sseq
    @2
    cS
    c0g
    cfv
    #
    @3
    wcel
    #
    @7
    @2
    @25
    @24
    @5
    wcel
    #
    @24
    cF
    cfv
    #
    cV
    wcel
    #
    @2
    cS
    cgrp
    wcel
    #
    @26
    @0
    @29
    @1
    cS
    cT
    cF
    ghmgrp1
    #
    adantr
    #
    @5
    cS
    @24
    @22
    @24
    eqid
    #
    grpidcl
    syl
    @2
    @27
    cT
    c0g
    cfv
    #
    cV
    @0
    @27
    @33
    wceq
    @1
    cS
    cT
    cF
    @24
    @33
    @32
    @33
    eqid
    #
    ghmid
    adantr
    @1
    @33
    cV
    wcel
    @0
    cV
    cT
    @33
    @34
    subg0cl
    adantl
    eqeltrd
    @2
    cF
    @5
    wfn
    #
    @25
    @26
    @28
    wa
    wb
    @2
    @21
    @35
    @23
    @5
    @20
    cF
    ffn
    syl
    #
    @5
    @24
    cV
    cF
    elpreima
    syl
    mpbir2and
    @3
    @24
    ne0i
    syl
    @2
    @17
    va
    @3
    @2
    @8
    @3
    wcel
    #
    @8
    @5
    wcel
    #
    @8
    cF
    cfv
    #
    cV
    wcel
    #
    wa
    #
    @17
    @2
    @35
    @37
    @41
    wb
    @36
    @5
    @8
    cV
    cF
    elpreima
    syl
    @2
    @41
    @17
    @2
    @41
    wa
    #
    @13
    @16
    @42
    @12
    vb
    @3
    @42
    @9
    @3
    wcel
    #
    @9
    @5
    wcel
    #
    @9
    cF
    cfv
    #
    cV
    wcel
    #
    wa
    #
    @12
    @2
    @43
    @47
    wb
    #
    @41
    @2
    @35
    @48
    @36
    @5
    @9
    cV
    cF
    elpreima
    syl
    adantr
    @2
    @41
    @47
    @12
    @2
    @41
    @47
    wa
    #
    wa
    #
    @12
    @11
    @5
    wcel
    #
    @11
    cF
    cfv
    #
    cV
    wcel
    #
    @50
    @29
    @38
    @44
    @51
    @0
    @29
    @1
    @49
    @30
    ad2antrr
    @2
    @38
    @40
    @47
    simprll
    #
    @2
    @41
    @44
    @46
    simprrl
    #
    @5
    @10
    cS
    @8
    @9
    @22
    @10
    eqid
    #
    grpcl
    syl3anc
    @50
    @52
    @39
    @45
    cT
    cplusg
    cfv
    #
    co
    #
    cV
    @50
    @0
    @38
    @44
    @52
    @58
    wceq
    @0
    @1
    @49
    simpll
    @54
    @55
    @10
    @57
    cS
    cT
    @8
    cF
    @9
    @5
    @22
    @56
    @57
    eqid
    #
    ghmlin
    syl3anc
    @50
    @1
    @40
    @46
    @58
    cV
    wcel
    @0
    @1
    @49
    simplr
    @2
    @38
    @40
    @47
    simprlr
    @2
    @41
    @44
    @46
    simprrr
    @57
    cV
    cT
    @39
    @45
    @59
    subgcl
    syl3anc
    eqeltrd
    @2
    @12
    @51
    @53
    wa
    wb
    #
    @49
    @2
    @35
    @60
    @36
    @5
    @11
    cV
    cF
    elpreima
    syl
    adantr
    mpbir2and
    expr
    sylbid
    ralrimiv
    @42
    @16
    @15
    @5
    wcel
    #
    @15
    cF
    cfv
    #
    cV
    wcel
    #
    @42
    @29
    @38
    @61
    @2
    @29
    @41
    @31
    adantr
    @2
    @38
    @40
    simprl
    @5
    cS
    @14
    @8
    @22
    @14
    eqid
    #
    grpinvcl
    syl2anc
    @42
    @62
    @39
    cT
    cminusg
    cfv
    #
    cfv
    #
    cV
    @0
    @38
    @62
    @66
    wceq
    @1
    @40
    @5
    cS
    cT
    cF
    @14
    @65
    @8
    @22
    @64
    @65
    eqid
    #
    ghminv
    ad2ant2r
    @1
    @40
    @66
    cV
    wcel
    @0
    @38
    cV
    cT
    @65
    @39
    @67
    subginvcl
    ad2ant2l
    eqeltrd
    @2
    @16
    @61
    @63
    wa
    wb
    #
    @41
    @2
    @35
    @68
    @36
    @5
    @15
    cV
    cF
    elpreima
    syl
    adantr
    mpbir2and
    jca
    ex
    sylbid
    ralrimiv
    @2
    @29
    @4
    @6
    @7
    @18
    w3a
    wb
    @31
    va
    vb
    @5
    @10
    @3
    cS
    @14
    @22
    @56
    @64
    issubg2
    syl
    mpbir3and
end
