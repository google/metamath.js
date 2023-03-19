include "ctgp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wa.mm"
include "ccl.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "csg.mm"
include "co.mm"
include "wral.mm"
include "cuni.mm"
include "ctop.mm"
include "ctopon.mm"
include "eqid.mm"
include "tgptopon.mm"
include "adantr.mm"
include "topontop.mm"
include "syl.mm"
include "subgss.mm"
include "adantl.mm"
include "wceq.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "clsss3.mm"
include "syl2anc.mm"
include "sseqtr4d.mm"
include "sscls.mm"
include "c0g.mm"
include "subg0cl.mm"
include "ne0i.mm"
include "ssn0.mm"
include "cop.mm"
include "df-ov.mm"
include "cxp.mm"
include "ccnv.mm"
include "cima.mm"
include "opelxpi.mm"
include "ctx.mm"
include "txcls.mm"
include "syl22anc.mm"
include "txtopon.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "cgrp.mm"
include "tgpgrp.mm"
include "grpsubf.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "subgsubcl.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "ralxp.mm"
include "sylibr.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "xpss12.mm"
include "funimass5.mm"
include "mpbird.mm"
include "clsss.mm"
include "syl3anc.mm"
include "ccn.mm"
include "tgpsubcn.mm"
include "cncls2i.mm"
include "sstrd.mm"
include "eqsstr3d.mm"
include "sselda.mm"
include "sylan2.mm"
include "wfn.mm"
include "ad2antrr.mm"
include "ffn.mm"
include "elpreima.mm"
include "4syl.mm"
include "mpbid.mm"
include "simprd.mm"
include "syl5eqel.mm"
include "w3a.mm"
include "issubg4.mm"
include "mpbir3and.mm"

theorem clssubg
  let cS: class S
  let cG: class G
  let cJ: class J
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cR: class R
  let cX: class X
  assume subgntr.h: |- J = ( TopOpen ` G )


  assert |- ( ( G e. TopGrp /\ S e. ( SubGrp ` G ) ) -> ( ( cls ` J ) ` S ) e. ( SubGrp ` G ) )

  proof
    cG
    ctgp
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
    cS
    cJ
    ccl
    cfv
    cfv
    #
    @1
    wcel
    #
    @4
    cG
    cbs
    cfv
    #
    wss
    #
    @4
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    csg
    cfv
    #
    co
    #
    @4
    wcel
    #
    vy
    @4
    wral
    vx
    @4
    wral
    #
    @3
    @4
    cJ
    cuni
    #
    @6
    @3
    cJ
    ctop
    wcel
    #
    cS
    @15
    wss
    #
    @4
    @15
    wss
    @3
    cJ
    @6
    ctopon
    cfv
    wcel
    #
    @16
    @0
    @18
    @2
    cG
    cJ
    @6
    subgntr.h
    @6
    eqid
    #
    tgptopon
    adantr
    #
    @6
    cJ
    topontop
    syl
    #
    @3
    cS
    @6
    @15
    @2
    cS
    @6
    wss
    #
    @0
    @6
    cS
    cG
    @19
    subgss
    adantl
    #
    @3
    @18
    @6
    @15
    wceq
    @20
    @6
    cJ
    toponuni
    syl
    #
    sseqtrd
    #
    cS
    cJ
    @15
    @15
    eqid
    #
    clsss3
    syl2anc
    @24
    sseqtr4d
    @3
    cS
    @4
    wss
    #
    cS
    c0
    wne
    #
    @8
    @3
    @16
    @17
    @27
    @21
    @25
    cS
    cJ
    @15
    @26
    sscls
    syl2anc
    @3
    cG
    c0g
    cfv
    #
    cS
    wcel
    #
    @28
    @2
    @30
    @0
    cS
    cG
    @29
    @29
    eqid
    subg0cl
    adantl
    cS
    @29
    ne0i
    syl
    cS
    @4
    ssn0
    syl2anc
    @3
    @13
    vx
    vy
    @4
    @4
    @3
    @9
    @4
    wcel
    @10
    @4
    wcel
    wa
    #
    wa
    #
    @12
    @9
    @10
    cop
    #
    @11
    cfv
    #
    @4
    @9
    @10
    @11
    df-ov
    #
    @32
    @33
    @6
    @6
    cxp
    #
    wcel
    #
    @34
    @4
    wcel
    #
    @32
    @33
    @11
    ccnv
    #
    @4
    cima
    #
    wcel
    #
    @37
    @38
    wa
    #
    @31
    @3
    @33
    @4
    @4
    cxp
    #
    wcel
    @41
    @9
    @10
    @4
    @4
    opelxpi
    @3
    @43
    @40
    @33
    @3
    @43
    cS
    cS
    cxp
    #
    cJ
    cJ
    ctx
    co
    #
    ccl
    cfv
    #
    cfv
    #
    @40
    @3
    @18
    @18
    @22
    @22
    @47
    @43
    wceq
    @20
    @20
    @23
    @23
    cS
    cS
    cJ
    cJ
    @6
    @6
    txcls
    syl22anc
    @3
    @47
    @39
    cS
    cima
    #
    @46
    cfv
    #
    @40
    @3
    @45
    ctop
    wcel
    #
    @48
    @45
    cuni
    #
    wss
    @44
    @48
    wss
    #
    @47
    @49
    wss
    @3
    @45
    @36
    ctopon
    cfv
    wcel
    #
    @50
    @3
    @18
    @18
    @53
    @20
    @20
    cJ
    cJ
    @6
    @6
    txtopon
    syl2anc
    #
    @36
    @45
    topontop
    syl
    @3
    @48
    @36
    @51
    @3
    @11
    cdm
    #
    @48
    @36
    @11
    cS
    cnvimass
    @3
    @36
    @6
    @11
    wf
    #
    @55
    @36
    wceq
    @3
    cG
    cgrp
    wcel
    #
    @56
    @0
    @57
    @2
    cG
    tgpgrp
    #
    adantr
    #
    @6
    cG
    @11
    @19
    @11
    eqid
    #
    grpsubf
    #
    syl
    #
    @36
    @6
    @11
    fdm
    syl
    #
    syl5sseq
    @3
    @53
    @36
    @51
    wceq
    @54
    @36
    @45
    toponuni
    syl
    sseqtrd
    @3
    @52
    vz
    cv
    #
    @11
    cfv
    #
    cS
    wcel
    #
    vz
    @44
    wral
    #
    @2
    @67
    @0
    @2
    @12
    cS
    wcel
    #
    vy
    cS
    wral
    vx
    cS
    wral
    @67
    @2
    @68
    vx
    vy
    cS
    cS
    @2
    @9
    cS
    wcel
    @10
    cS
    wcel
    @68
    cS
    cG
    @11
    @9
    @10
    @60
    subgsubcl
    3expb
    ralrimivva
    @66
    @68
    vz
    vx
    vy
    cS
    cS
    @64
    @33
    wceq
    #
    @65
    @12
    cS
    @69
    @65
    @34
    @12
    @64
    @33
    @11
    fveq2
    @35
    syl6eqr
    eleq1d
    ralxp
    sylibr
    adantl
    @3
    @11
    wfun
    #
    @44
    @55
    wss
    @52
    @67
    wb
    @3
    @56
    @70
    @62
    @36
    @6
    @11
    ffun
    syl
    @3
    @44
    @36
    @55
    @3
    @22
    @22
    @44
    @36
    wss
    @23
    @23
    cS
    @6
    cS
    @6
    xpss12
    syl2anc
    @63
    sseqtr4d
    vz
    @44
    cS
    @11
    funimass5
    syl2anc
    mpbird
    @48
    @44
    @45
    @51
    @51
    eqid
    clsss
    syl3anc
    @3
    @11
    @45
    cJ
    ccn
    co
    wcel
    #
    @17
    @49
    @40
    wss
    @0
    @71
    @2
    cG
    cJ
    @11
    subgntr.h
    @60
    tgpsubcn
    adantr
    @25
    cS
    @11
    @45
    cJ
    @15
    @26
    cncls2i
    syl2anc
    sstrd
    eqsstr3d
    sselda
    sylan2
    @32
    @57
    @56
    @11
    @36
    wfn
    @41
    @42
    wb
    @0
    @57
    @2
    @31
    @58
    ad2antrr
    @61
    @36
    @6
    @11
    ffn
    @36
    @33
    @4
    @11
    elpreima
    4syl
    mpbid
    simprd
    syl5eqel
    ralrimivva
    @3
    @57
    @5
    @7
    @8
    @14
    w3a
    wb
    @59
    vx
    vy
    @6
    @4
    cG
    @11
    @19
    @60
    issubg4
    syl
    mpbir3and
end
