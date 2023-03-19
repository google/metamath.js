include "cres.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "wss.mm"
include "cgrp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "ccntz.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cima.mm"
include "cuni.mm"
include "cmrc.mm"
include "cin.mm"
include "c0g.mm"
include "wceq.mm"
include "wa.mm"
include "dprdgrp.mm"
include "syl.mm"
include "dprdf2.mm"
include "fssresd.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "sseldd.mm"
include "eldifi.mm"
include "adantl.mm"
include "wne.mm"
include "eldifsni.mm"
include "necomd.mm"
include "eqid.mm"
include "dprdcntz.mm"
include "fvres.mm"
include "fveq2d.mm"
include "3sstr4d.mm"
include "ralrimiva.mm"
include "ineq1d.mm"
include "cbs.mm"
include "cmre.mm"
include "cacs.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "adantr.mm"
include "resss.mm"
include "imass1.mm"
include "ax-mp.mm"
include "ssdif.mm"
include "imass2.mm"
include "syl5ss.mm"
include "unissd.mm"
include "cpw.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "subgss.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"
include "syl6ss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "mrcssd.mm"
include "sslin.mm"
include "sselda.mm"
include "dprddisj.mm"
include "sseqtrd.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "subg0cl.mm"
include "sstrd.mm"
include "mrccl.mm"
include "syl2anc.mm"
include "elind.mm"
include "snssd.mm"
include "eqssd.mm"
include "eqtrd.mm"
include "jca.mm"
include "cvv.mm"
include "w3a.mm"
include "wb.mm"
include "dprddomcld.mm"
include "ssexd.mm"
include "fdm.mm"
include "dmdprd.mm"
include "mpbir3and.mm"
include "rnss.mm"
include "uniss.mm"
include "mp2b.mm"
include "a1i.mm"
include "dprdspan.mm"

theorem dprdres
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cG: class G
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  assume dprdres.1: |- ( ph -> G dom DProd S )
  assume dprdres.2: |- ( ph -> dom S = I )
  assume dprdres.3: |- ( ph -> A C_ I )


  assert |- ( ph -> ( G dom DProd ( S |` A ) /\ ( G DProd ( S |` A ) ) C_ ( G DProd S ) ) )

  proof
    wph
    cG
    cS
    cA
    cres
    #
    cdprd
    cdm
    #
    wbr
    #
    cG
    @0
    cdprd
    co
    #
    cG
    cS
    cdprd
    co
    #
    wss
    wph
    @2
    cG
    cgrp
    wcel
    #
    cA
    cG
    csubg
    cfv
    #
    @0
    wf
    #
    vx
    cv
    #
    @0
    cfv
    #
    vy
    cv
    #
    @0
    cfv
    #
    cG
    ccntz
    cfv
    #
    cfv
    #
    wss
    #
    vy
    cA
    @8
    csn
    #
    cdif
    #
    wral
    #
    @9
    @0
    @16
    cima
    #
    cuni
    #
    @6
    cmrc
    cfv
    #
    cfv
    #
    cin
    #
    cG
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    wa
    #
    vx
    cA
    wral
    #
    wph
    cG
    cS
    @1
    wbr
    #
    @5
    dprdres.1
    cS
    cG
    dprdgrp
    syl
    #
    wph
    cI
    @6
    cA
    cS
    wph
    cS
    cG
    cI
    dprdres.1
    dprdres.2
    dprdf2
    #
    dprdres.3
    fssresd
    #
    wph
    @26
    vx
    cA
    wph
    @8
    cA
    wcel
    #
    wa
    #
    @17
    @25
    @33
    @14
    vy
    @16
    @33
    @10
    @16
    wcel
    #
    wa
    #
    @8
    cS
    cfv
    #
    @10
    cS
    cfv
    #
    @12
    cfv
    @9
    @13
    @35
    cS
    cG
    cI
    @8
    @10
    @12
    wph
    @28
    @32
    @34
    dprdres.1
    ad2antrr
    wph
    cS
    cdm
    cI
    wceq
    #
    @32
    @34
    dprdres.2
    ad2antrr
    @35
    cA
    cI
    @8
    wph
    cA
    cI
    wss
    #
    @32
    @34
    dprdres.3
    ad2antrr
    #
    wph
    @32
    @34
    simplr
    #
    sseldd
    @35
    cA
    cI
    @10
    @40
    @34
    @10
    cA
    wcel
    #
    @33
    @10
    cA
    @15
    eldifi
    adantl
    #
    sseldd
    @35
    @10
    @8
    @34
    @10
    @8
    wne
    @33
    @10
    cA
    @8
    eldifsni
    adantl
    necomd
    @12
    eqid
    #
    dprdcntz
    @35
    @32
    @9
    @36
    wceq
    #
    @41
    @8
    cA
    cS
    fvres
    #
    syl
    @35
    @11
    @37
    @12
    @35
    @42
    @11
    @37
    wceq
    @43
    @10
    cA
    cS
    fvres
    syl
    fveq2d
    3sstr4d
    ralrimiva
    @33
    @22
    @36
    @21
    cin
    #
    @24
    @33
    @9
    @36
    @21
    @32
    @45
    wph
    @46
    adantl
    ineq1d
    @33
    @47
    @24
    @33
    @47
    @36
    cS
    cI
    @15
    cdif
    #
    cima
    #
    cuni
    #
    @20
    cfv
    #
    cin
    #
    @24
    @33
    @21
    @51
    wss
    @47
    @52
    wss
    @33
    @6
    @19
    @20
    @50
    cG
    cbs
    cfv
    #
    wph
    @6
    @53
    cmre
    cfv
    wcel
    #
    @32
    wph
    @5
    @6
    @53
    cacs
    cfv
    wcel
    @54
    @29
    @53
    cG
    @53
    eqid
    #
    subgacs
    @6
    @53
    acsmre
    3syl
    #
    adantr
    #
    @20
    eqid
    #
    @33
    @18
    @49
    @33
    @18
    cS
    @16
    cima
    #
    @49
    @0
    cS
    wss
    #
    @18
    @59
    wss
    cS
    cA
    resss
    #
    @0
    cS
    @16
    imass1
    ax-mp
    @33
    @39
    @16
    @48
    wss
    @59
    @49
    wss
    wph
    @39
    @32
    dprdres.3
    adantr
    cA
    cI
    @15
    ssdif
    @16
    @48
    cS
    imass2
    3syl
    syl5ss
    unissd
    #
    @33
    @49
    @53
    cpw
    #
    wss
    @50
    @53
    wss
    @33
    @49
    cS
    crn
    #
    @63
    cS
    @48
    imassrn
    wph
    @64
    @63
    wss
    #
    @32
    wph
    @64
    @6
    @63
    wph
    cI
    @6
    cS
    wf
    @64
    @6
    wss
    @30
    cI
    @6
    cS
    frn
    syl
    vx
    @6
    @63
    @8
    @6
    wcel
    @8
    @53
    wss
    @8
    @63
    wcel
    @53
    @8
    cG
    @55
    subgss
    vx
    @53
    selpw
    sylibr
    ssriv
    syl6ss
    #
    adantr
    syl5ss
    @49
    @53
    sspwuni
    sylib
    #
    mrcssd
    @21
    @51
    @36
    sslin
    syl
    @33
    cS
    cG
    cI
    @20
    @8
    @23
    wph
    @28
    @32
    dprdres.1
    adantr
    wph
    @38
    @32
    dprdres.2
    adantr
    wph
    cA
    cI
    @8
    dprdres.3
    sselda
    #
    @23
    eqid
    #
    @58
    dprddisj
    sseqtrd
    @33
    @23
    @47
    @33
    @36
    @21
    @23
    @33
    @36
    @6
    wcel
    #
    @23
    @36
    wcel
    wph
    @32
    @8
    cI
    wcel
    @70
    @68
    wph
    cI
    @6
    @8
    cS
    @30
    ffvelrnda
    syldan
    @36
    cG
    @23
    @69
    subg0cl
    syl
    @33
    @21
    @6
    wcel
    #
    @23
    @21
    wcel
    @33
    @54
    @19
    @53
    wss
    @71
    @57
    @33
    @19
    @50
    @53
    @62
    @67
    sstrd
    @6
    @19
    @20
    @53
    @58
    mrccl
    syl2anc
    @21
    cG
    @23
    @69
    subg0cl
    syl
    elind
    snssd
    eqssd
    eqtrd
    jca
    ralrimiva
    wph
    cA
    cvv
    wcel
    @0
    cdm
    cA
    wceq
    #
    @2
    @5
    @7
    @27
    w3a
    wb
    wph
    cA
    cI
    cvv
    wph
    cS
    cG
    cI
    dprdres.1
    dprdres.2
    dprddomcld
    dprdres.3
    ssexd
    wph
    @7
    @72
    @31
    cA
    @6
    @0
    fdm
    syl
    vx
    vy
    @0
    cG
    cA
    @20
    cvv
    @23
    @12
    @44
    @69
    @58
    dmdprd
    syl2anc
    mpbir3and
    #
    wph
    @0
    crn
    #
    cuni
    #
    @20
    cfv
    #
    @64
    cuni
    #
    @20
    cfv
    #
    @3
    @4
    wph
    @6
    @75
    @20
    @77
    @53
    @56
    @58
    @75
    @77
    wss
    #
    wph
    @60
    @74
    @64
    wss
    @79
    @61
    @0
    cS
    rnss
    @74
    @64
    uniss
    mp2b
    a1i
    wph
    @65
    @77
    @53
    wss
    @66
    @64
    @53
    sspwuni
    sylib
    mrcssd
    wph
    @2
    @3
    @76
    wceq
    @73
    @0
    cG
    @20
    @58
    dprdspan
    syl
    wph
    @28
    @4
    @78
    wceq
    dprdres.1
    cS
    cG
    @20
    @58
    dprdspan
    syl
    3sstr4d
    jca
end
