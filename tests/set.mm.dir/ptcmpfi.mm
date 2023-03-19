include "cfn.mm"
include "wcel.mm"
include "ccmp.mm"
include "wf.mm"
include "wa.mm"
include "cres.mm"
include "cpt.mm"
include "cfv.mm"
include "wceq.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "syl.mm"
include "adantl.mm"
include "fveq2d.mm"
include "wss.mm"
include "wi.mm"
include "ssid.mm"
include "cv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "sseq1.mm"
include "reseq2.mm"
include "res0.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "imbi12d.mm"
include "ctop.mm"
include "cin.mm"
include "cvv.mm"
include "0ex.mm"
include "f0.mm"
include "pttop.mm"
include "mp2an.mm"
include "cuni.mm"
include "cpw.mm"
include "cixp.mm"
include "eqid.mm"
include "ptuni.mm"
include "ixp0x.mm"
include "snfi.mm"
include "eqeltri.mm"
include "eqeltrri.mm"
include "pwfi.mm"
include "mpbi.mm"
include "pwuni.mm"
include "ssfi.mm"
include "elin.mm"
include "mpbir2an.mm"
include "fincmp.mm"
include "ax-mp.mm"
include "2a1i.mm"
include "wn.mm"
include "ssun1.mm"
include "id.mm"
include "syl5ss.mm"
include "imim1i.mm"
include "ctx.mm"
include "co.mm"
include "chmph.mm"
include "wbr.mm"
include "cmpt2.mm"
include "chmeo.mm"
include "resabs1.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "ssun2.mm"
include "vex.mm"
include "snex.mm"
include "unex.mm"
include "a1i.mm"
include "simplr.mm"
include "cmptop.mm"
include "ssriv.mm"
include "fss.mm"
include "sylancl.mm"
include "simprr.mm"
include "fssresd.mm"
include "eqidd.mm"
include "simprl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "ptunhmeo.mm"
include "hmphi.mm"
include "cop.mm"
include "ad2antlr.mm"
include "snss.mm"
include "fnressn.mm"
include "syl2anc.mm"
include "cmpt.mm"
include "ctopon.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "toptopon.mm"
include "sylib.mm"
include "pt1hmeo.mm"
include "cmphmph.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "txcmp.mm"
include "expcom.mm"
include "sylsyld.mm"
include "a2d.mm"
include "ex.mm"
include "syl5.mm"
include "findcard2s.mm"
include "mpi.mm"
include "anabsi5.mm"
include "eqeltrrd.mm"

theorem ptcmpfi
  let cA: class A
  let cF: class F
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. Fin /\ F : A --> Comp ) -> ( Xt_ ` F ) e. Comp )

  proof
    cA
    cfn
    wcel
    #
    cA
    ccmp
    cF
    wf
    #
    wa
    #
    cF
    cA
    cres
    #
    cpt
    cfv
    #
    cF
    cpt
    cfv
    ccmp
    @2
    @3
    cF
    cpt
    @1
    @3
    cF
    wceq
    #
    @0
    @1
    cF
    cA
    wfn
    #
    @5
    cA
    ccmp
    cF
    ffn
    #
    cA
    cF
    fnresdm
    syl
    adantl
    fveq2d
    @0
    @1
    @4
    ccmp
    wcel
    #
    @0
    cA
    cA
    wss
    #
    @2
    @8
    wi
    #
    cA
    ssid
    vx
    cv
    #
    cA
    wss
    #
    @2
    cF
    @11
    cres
    #
    cpt
    cfv
    #
    ccmp
    wcel
    #
    wi
    #
    wi
    c0
    cA
    wss
    #
    @2
    c0
    cpt
    cfv
    #
    ccmp
    wcel
    #
    wi
    #
    wi
    vy
    cv
    #
    cA
    wss
    #
    @2
    cF
    @21
    cres
    #
    cpt
    cfv
    #
    ccmp
    wcel
    #
    wi
    #
    wi
    #
    @21
    vz
    cv
    #
    csn
    #
    cun
    #
    cA
    wss
    #
    @2
    cF
    @30
    cres
    #
    cpt
    cfv
    #
    ccmp
    wcel
    #
    wi
    #
    wi
    #
    @9
    @10
    wi
    vx
    vy
    vz
    cA
    @11
    c0
    wceq
    #
    @12
    @17
    @16
    @20
    @11
    c0
    cA
    sseq1
    @37
    @15
    @19
    @2
    @37
    @14
    @18
    ccmp
    @37
    @13
    c0
    cpt
    @37
    @13
    cF
    c0
    cres
    c0
    @11
    c0
    cF
    reseq2
    cF
    res0
    syl6eq
    fveq2d
    eleq1d
    imbi2d
    imbi12d
    @11
    @21
    wceq
    #
    @12
    @22
    @16
    @26
    @11
    @21
    cA
    sseq1
    @38
    @15
    @25
    @2
    @38
    @14
    @24
    ccmp
    @38
    @13
    @23
    cpt
    @11
    @21
    cF
    reseq2
    fveq2d
    eleq1d
    imbi2d
    imbi12d
    @11
    @30
    wceq
    #
    @12
    @31
    @16
    @35
    @11
    @30
    cA
    sseq1
    @39
    @15
    @34
    @2
    @39
    @14
    @33
    ccmp
    @39
    @13
    @32
    cpt
    @11
    @30
    cF
    reseq2
    fveq2d
    eleq1d
    imbi2d
    imbi12d
    @11
    cA
    wceq
    #
    @12
    @9
    @16
    @10
    @11
    cA
    cA
    sseq1
    @40
    @15
    @8
    @2
    @40
    @14
    @4
    ccmp
    @40
    @13
    @3
    cpt
    @11
    cA
    cF
    reseq2
    fveq2d
    eleq1d
    imbi2d
    imbi12d
    @19
    @17
    @2
    @18
    ctop
    cfn
    cin
    wcel
    #
    @19
    @41
    @18
    ctop
    wcel
    #
    @18
    cfn
    wcel
    #
    c0
    cvv
    wcel
    #
    c0
    ctop
    c0
    wf
    #
    @42
    0ex
    ctop
    f0
    #
    c0
    c0
    cvv
    pttop
    mp2an
    @18
    cuni
    #
    cpw
    #
    cfn
    wcel
    #
    @18
    @48
    wss
    @43
    @47
    cfn
    wcel
    @49
    vx
    c0
    @11
    c0
    cfv
    cuni
    #
    cixp
    #
    @47
    cfn
    @44
    @45
    @51
    @47
    wceq
    0ex
    @46
    vx
    c0
    c0
    @18
    cvv
    @18
    eqid
    ptuni
    mp2an
    @51
    c0
    csn
    cfn
    vx
    @50
    ixp0x
    c0
    snfi
    eqeltri
    eqeltrri
    @47
    pwfi
    mpbi
    @18
    pwuni
    @48
    @18
    ssfi
    mp2an
    @18
    ctop
    cfn
    elin
    mpbir2an
    @18
    fincmp
    ax-mp
    2a1i
    @28
    @21
    wcel
    wn
    #
    @27
    @36
    wi
    @21
    cfn
    wcel
    @27
    @31
    @26
    wi
    @52
    @36
    @31
    @22
    @26
    @31
    @21
    @30
    cA
    @21
    @29
    ssun1
    #
    @31
    id
    syl5ss
    imim1i
    @52
    @31
    @26
    @35
    @52
    @31
    @26
    @35
    wi
    @52
    @31
    wa
    #
    @2
    @25
    @34
    @2
    @54
    @25
    @34
    wi
    @2
    @54
    wa
    #
    @24
    cF
    @29
    cres
    #
    cpt
    cfv
    #
    ctx
    co
    #
    @33
    chmph
    wbr
    #
    @25
    @58
    ccmp
    wcel
    #
    @34
    @55
    vu
    vv
    @24
    cuni
    #
    @57
    cuni
    #
    vu
    cv
    vv
    cv
    cun
    cmpt2
    #
    @58
    @33
    chmeo
    co
    wcel
    @59
    @55
    vu
    vv
    @21
    @29
    @30
    @32
    @63
    @33
    @24
    @57
    cvv
    @61
    @62
    @61
    eqid
    @62
    eqid
    @33
    eqid
    @23
    @32
    @21
    cres
    #
    cpt
    @64
    @23
    @21
    @30
    wss
    @64
    @23
    wceq
    @53
    cF
    @21
    @30
    resabs1
    ax-mp
    eqcomi
    fveq2i
    @56
    @32
    @29
    cres
    #
    cpt
    @65
    @56
    @29
    @30
    wss
    @65
    @56
    wceq
    @29
    @21
    ssun2
    #
    cF
    @29
    @30
    resabs1
    ax-mp
    eqcomi
    fveq2i
    @63
    eqid
    @30
    cvv
    wcel
    @55
    @21
    @29
    vy
    vex
    @28
    snex
    unex
    a1i
    @55
    cA
    ctop
    @30
    cF
    @55
    @1
    ccmp
    ctop
    wss
    cA
    ctop
    cF
    wf
    @0
    @1
    @54
    simplr
    #
    vx
    ccmp
    ctop
    @11
    cmptop
    ssriv
    #
    cA
    ccmp
    ctop
    cF
    fss
    sylancl
    @2
    @52
    @31
    simprr
    #
    fssresd
    @55
    @30
    eqidd
    @55
    @52
    @21
    @29
    cin
    c0
    wceq
    @2
    @52
    @31
    simprl
    @21
    @28
    disjsn
    sylibr
    ptunhmeo
    @63
    @58
    @33
    hmphi
    syl
    @55
    @57
    ccmp
    wcel
    #
    @25
    @60
    wi
    @55
    @57
    @28
    @28
    cF
    cfv
    #
    cop
    csn
    #
    cpt
    cfv
    #
    ccmp
    @55
    @56
    @72
    cpt
    @55
    @6
    @28
    cA
    wcel
    #
    @56
    @72
    wceq
    @1
    @6
    @0
    @54
    @7
    ad2antlr
    @55
    @29
    cA
    wss
    @74
    @55
    @29
    @30
    cA
    @66
    @69
    syl5ss
    @28
    cA
    vz
    vex
    #
    snss
    sylibr
    #
    cA
    @28
    cF
    fnressn
    syl2anc
    fveq2d
    @55
    @71
    @73
    chmph
    wbr
    #
    @71
    ccmp
    wcel
    @73
    ccmp
    wcel
    @55
    vx
    @71
    cuni
    #
    @28
    @11
    cop
    csn
    cmpt
    #
    @71
    @73
    chmeo
    co
    wcel
    @77
    @55
    vx
    @28
    @71
    @73
    cvv
    @78
    @73
    eqid
    @28
    cvv
    wcel
    @55
    @75
    a1i
    @55
    @71
    ctop
    wcel
    @71
    @78
    ctopon
    cfv
    wcel
    @55
    ccmp
    ctop
    @71
    @68
    @55
    cA
    ccmp
    @28
    cF
    @67
    @76
    ffvelrnd
    #
    sseldi
    @71
    @78
    @78
    eqid
    toptopon
    sylib
    pt1hmeo
    @79
    @71
    @73
    hmphi
    syl
    @80
    @71
    @73
    cmphmph
    sylc
    eqeltrd
    @25
    @70
    @60
    @24
    @57
    txcmp
    expcom
    syl
    @58
    @33
    cmphmph
    sylsyld
    expcom
    a2d
    ex
    a2d
    syl5
    adantl
    findcard2s
    mpi
    anabsi5
    eqeltrrd
end
