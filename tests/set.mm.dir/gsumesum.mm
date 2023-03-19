include "cesum.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "nfcv.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "esumval.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "iccssxr.mm"
include "xrge0base.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "ex.mm"
include "ralrimi.mm"
include "gsummptcl.mm"
include "sseldi.mm"
include "wceq.mm"
include "wrex.mm"
include "pwidg.mm"
include "syl.mm"
include "elind.mm"
include "mpteq1.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eqid.mm"
include "ovex.mm"
include "elrnmpti.mm"
include "sylibr.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "simpr.mm"
include "cbvmptv.mm"
include "sylib.mm"
include "cdif.mm"
include "cxad.mm"
include "inss2.mm"
include "nfv.mm"
include "nfan.mm"
include "wel.mm"
include "simpll.mm"
include "wss.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "ad2antlr.mm"
include "sseldd.mm"
include "diffi.mm"
include "adantr.mm"
include "eldifad.mm"
include "elxrge0.mm"
include "simprbi.mm"
include "xraddge02.mm"
include "imp.mm"
include "syl21anc.mm"
include "adantlr.mm"
include "adantl.mm"
include "cres.mm"
include "xrge00.mm"
include "xrge0plusg.mm"
include "wf.mm"
include "fmptdf.mm"
include "cfsupp.mm"
include "cvv.mm"
include "wfn.mm"
include "fnmpt.mm"
include "c0ex.mm"
include "fndmfifsupp.mm"
include "c0.mm"
include "disjdif.mm"
include "cun.mm"
include "undif.mm"
include "biimpi.mm"
include "eqcomd.mm"
include "gsumsplit.mm"
include "resmpt.mm"
include "difss.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "ralrimiva.mm"
include "r19.29r.mm"
include "breq1.mm"
include "biimpar.mm"
include "rexlimivw.mm"
include "wb.mm"
include "rnmptss.mm"
include "sselda.mm"
include "xrltnle.mm"
include "con2bid.mm"
include "mpbid.mm"
include "supmax.mm"
include "eqtr2d.mm"

theorem gsumesum
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  assume gsumesum.0: |- F/ k ph
  assume gsumesum.1: |- ( ph -> A e. Fin )
  assume gsumesum.2: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )

  disjoint A k
  disjoint a k
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B a
  disjoint B x
  disjoint B y
  disjoint a ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( ( RR*s |`s ( 0 [,] +oo ) ) gsum ( k e. A |-> B ) ) = sum* k e. A B )

  proof
    wph
    cA
    cB
    vk
    cesum
    vx
    cA
    cpw
    #
    cfn
    cin
    #
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    vk
    vx
    cv
    #
    cB
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    @3
    vk
    cA
    cB
    cmpt
    #
    cgsu
    co
    #
    wph
    vx
    cA
    cB
    @6
    vk
    cfn
    gsumesum.0
    vk
    cA
    nfcv
    gsumesum.1
    gsumesum.2
    wph
    @4
    @1
    wcel
    #
    wa
    #
    @6
    eqidd
    esumval
    wph
    vy
    cxr
    @8
    @10
    clt
    cxr
    clt
    wor
    wph
    xrltso
    a1i
    wph
    @2
    cxr
    @10
    cc0
    cpnf
    iccssxr
    #
    wph
    @2
    vk
    @3
    cA
    cB
    xrge0base
    @3
    ccmn
    wcel
    #
    wph
    xrge0cmn
    a1i
    gsumesum.1
    wph
    cB
    @2
    wcel
    #
    vk
    cA
    gsumesum.0
    wph
    vk
    cv
    #
    cA
    wcel
    #
    @15
    gsumesum.2
    ex
    ralrimi
    #
    gsummptcl
    sseldi
    #
    wph
    @10
    @6
    wceq
    #
    vx
    @1
    wrex
    #
    @10
    @8
    wcel
    wph
    cA
    @1
    wcel
    @10
    @10
    wceq
    #
    @21
    wph
    @0
    cfn
    cA
    wph
    cA
    cfn
    wcel
    #
    cA
    @0
    wcel
    gsumesum.1
    cA
    cfn
    pwidg
    syl
    gsumesum.1
    elind
    wph
    @10
    eqidd
    @20
    @22
    vx
    cA
    @1
    @4
    cA
    wceq
    #
    @6
    @10
    @10
    @24
    @5
    @9
    @3
    cgsu
    vk
    @4
    cA
    cB
    mpteq1
    oveq2d
    eqeq2d
    rspcev
    syl2anc
    vx
    @1
    @6
    @10
    @7
    @7
    eqid
    #
    @3
    @5
    cgsu
    ovex
    elrnmpti
    sylibr
    wph
    vy
    cv
    #
    @8
    wcel
    #
    wa
    #
    @26
    @10
    cle
    wbr
    #
    @10
    @26
    clt
    wbr
    #
    wn
    #
    @28
    @26
    @3
    vk
    va
    cv
    #
    cB
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    va
    @1
    wrex
    #
    @34
    @10
    cle
    wbr
    #
    va
    @1
    wral
    #
    @29
    @28
    @27
    @36
    wph
    @27
    simpr
    va
    @1
    @34
    @26
    @7
    vx
    va
    @1
    @6
    @34
    @4
    @32
    wceq
    @5
    @33
    @3
    cgsu
    vk
    @4
    @32
    cB
    mpteq1
    oveq2d
    cbvmptv
    @3
    @33
    cgsu
    ovex
    elrnmpti
    sylib
    @28
    @37
    va
    @1
    @28
    @32
    @1
    wcel
    #
    wa
    #
    @34
    @34
    @3
    vk
    cA
    @32
    cdif
    #
    cB
    cmpt
    #
    cgsu
    co
    #
    cxad
    co
    #
    @10
    cle
    wph
    @39
    @34
    @44
    cle
    wbr
    #
    @27
    wph
    @39
    wa
    #
    @34
    cxr
    wcel
    #
    @43
    cxr
    wcel
    #
    cc0
    @43
    cle
    wbr
    #
    @45
    @46
    @2
    cxr
    @34
    @13
    @46
    @2
    vk
    @3
    @32
    cB
    xrge0base
    @14
    @46
    xrge0cmn
    a1i
    #
    @46
    @1
    cfn
    @32
    @0
    cfn
    inss2
    #
    wph
    @39
    simpr
    sseldi
    @46
    @15
    vk
    @32
    wph
    @39
    vk
    gsumesum.0
    @39
    vk
    nfv
    nfan
    #
    @46
    vk
    va
    wel
    #
    @15
    @46
    @53
    wa
    #
    wph
    @17
    @15
    wph
    @39
    @53
    simpll
    @54
    @32
    cA
    @16
    @39
    @32
    cA
    wss
    #
    wph
    @53
    @39
    @32
    cA
    @1
    @0
    @32
    @0
    cfn
    inss1
    #
    sseli
    elpwid
    #
    ad2antlr
    @46
    @53
    simpr
    sseldd
    gsumesum.2
    syl2anc
    ex
    ralrimi
    gsummptcl
    sseldi
    @46
    @2
    cxr
    @43
    @13
    @46
    @2
    vk
    @3
    @41
    cB
    xrge0base
    @50
    wph
    @41
    cfn
    wcel
    #
    @39
    wph
    @23
    @58
    gsumesum.1
    cA
    @32
    diffi
    syl
    adantr
    @46
    @15
    vk
    @41
    @52
    @46
    @16
    @41
    wcel
    #
    @15
    @46
    @59
    wa
    #
    wph
    @17
    @15
    wph
    @39
    @59
    simpll
    @60
    @16
    cA
    @32
    @46
    @59
    simpr
    eldifad
    gsumesum.2
    syl2anc
    ex
    ralrimi
    gsummptcl
    #
    sseldi
    @46
    @43
    @2
    wcel
    #
    @49
    @61
    @62
    @48
    @49
    @43
    elxrge0
    simprbi
    syl
    @47
    @48
    wa
    @49
    @45
    @34
    @43
    xraddge02
    imp
    syl21anc
    adantlr
    @40
    wph
    @55
    @10
    @44
    wceq
    wph
    @27
    @39
    simpll
    @39
    @55
    @28
    @57
    adantl
    wph
    @55
    wa
    #
    @10
    @3
    @9
    @32
    cres
    #
    cgsu
    co
    #
    @3
    @9
    @41
    cres
    #
    cgsu
    co
    #
    cxad
    co
    @44
    @63
    cA
    @2
    @32
    @41
    cxad
    @9
    @3
    cfn
    cc0
    xrge0base
    xrge00
    xrge0plusg
    @14
    @63
    xrge0cmn
    a1i
    wph
    @23
    @55
    gsumesum.1
    adantr
    wph
    cA
    @2
    @9
    wf
    @55
    wph
    vk
    cA
    cB
    @2
    @9
    gsumesum.0
    gsumesum.2
    @9
    eqid
    #
    fmptdf
    adantr
    wph
    @9
    cc0
    cfsupp
    wbr
    @55
    wph
    cA
    @9
    cvv
    cc0
    wph
    @15
    vk
    cA
    wral
    @9
    cA
    wfn
    @18
    vk
    cA
    cB
    @9
    @2
    @68
    fnmpt
    syl
    gsumesum.1
    cc0
    cvv
    wcel
    wph
    c0ex
    a1i
    fndmfifsupp
    adantr
    @32
    @41
    cin
    c0
    wceq
    @63
    @32
    cA
    disjdif
    a1i
    @55
    cA
    @32
    @41
    cun
    #
    wceq
    wph
    @55
    @69
    cA
    @55
    @69
    cA
    wceq
    @32
    cA
    undif
    biimpi
    eqcomd
    adantl
    gsumsplit
    @63
    @65
    @34
    @67
    @43
    cxad
    @55
    @65
    @34
    wceq
    wph
    @55
    @64
    @33
    @3
    cgsu
    vk
    cA
    @32
    cB
    resmpt
    oveq2d
    adantl
    @67
    @43
    wceq
    @63
    @66
    @42
    @3
    cgsu
    @41
    cA
    wss
    @66
    @42
    wceq
    cA
    @32
    difss
    vk
    cA
    @41
    cB
    resmpt
    ax-mp
    oveq2i
    a1i
    oveq12d
    eqtrd
    syl2anc
    breqtrrd
    ralrimiva
    @36
    @38
    wa
    @35
    @37
    wa
    #
    va
    @1
    wrex
    @29
    @35
    @37
    va
    @1
    r19.29r
    @70
    @29
    va
    @1
    @35
    @29
    @37
    @26
    @34
    @10
    cle
    breq1
    biimpar
    rexlimivw
    syl
    syl2anc
    @28
    @10
    cxr
    wcel
    #
    @26
    cxr
    wcel
    #
    @29
    @31
    wb
    wph
    @71
    @27
    @19
    adantr
    wph
    @8
    cxr
    @26
    wph
    @6
    cxr
    wcel
    #
    vx
    @1
    wral
    @8
    cxr
    wss
    wph
    @73
    vx
    @1
    @12
    @2
    cxr
    @6
    @13
    @12
    @2
    vk
    @3
    @4
    cB
    xrge0base
    @14
    @12
    xrge0cmn
    a1i
    @12
    @1
    cfn
    @4
    @51
    wph
    @11
    simpr
    sseldi
    @12
    @15
    vk
    @4
    wph
    @11
    vk
    gsumesum.0
    @11
    vk
    nfv
    nfan
    @12
    vk
    vx
    wel
    #
    @15
    @12
    @74
    wa
    #
    wph
    @17
    @15
    wph
    @11
    @74
    simpll
    @75
    @4
    cA
    @16
    @75
    @4
    cA
    @11
    @4
    @0
    wcel
    wph
    @74
    @1
    @0
    @4
    @56
    sseli
    ad2antlr
    elpwid
    @12
    @74
    simpr
    sseldd
    gsumesum.2
    syl2anc
    ex
    ralrimi
    gsummptcl
    sseldi
    ralrimiva
    vx
    @1
    @6
    cxr
    @7
    @25
    rnmptss
    syl
    sselda
    @71
    @72
    wa
    @30
    @29
    @10
    @26
    xrltnle
    con2bid
    syl2anc
    mpbid
    supmax
    eqtr2d
end
