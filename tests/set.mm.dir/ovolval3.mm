include "covol.mm"
include "cfv.mm"
include "cioo.mm"
include "cv.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "cabs.mm"
include "cmin.mm"
include "csumge0.mm"
include "wceq.mm"
include "wa.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "cxr.mm"
include "crab.mm"
include "clt.mm"
include "cinf.mm"
include "eqid.mm"
include "ovolval2.mm"
include "cvol.mm"
include "wcel.mm"
include "cmpt.mm"
include "c2nd.mm"
include "c1st.mm"
include "cop.mm"
include "wf.mm"
include "cvv.mm"
include "reex.mm"
include "xpex.mm"
include "inss2.mm"
include "mapss.mm"
include "mp2an.mm"
include "sseli.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqtrd.mm"
include "wbr.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "w3a.mm"
include "adantr.mm"
include "simpr.mm"
include "ovolfcl.mm"
include "syl2anc.mm"
include "simp3d.mm"
include "volioo.mm"
include "syl3anc.mm"
include "wfun.mm"
include "cdm.mm"
include "cpw.mm"
include "ioof.mm"
include "ffun.mm"
include "ax-mp.mm"
include "rexpssxrxp.mm"
include "sseldi.mm"
include "fdmi.mm"
include "eleqtrd.mm"
include "fvco.mm"
include "cc.mm"
include "recnd.mm"
include "cnmetdval.mm"
include "abssub.mm"
include "abssubge0d.mm"
include "3eqtrd.mm"
include "3eqtr4d.mm"
include "mpteq2dva.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "volioof.mm"
include "fssd.mm"
include "fcompt.mm"
include "absf.mm"
include "subf.mm"
include "fco.mm"
include "rr2sscn2.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexbiia.mm"
include "rabbii.mm"
include "eqtr2i.mm"
include "infeq1i.mm"

theorem ovolval3
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let cM: class M
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x
  assume ovolval3.a: |- ( ph -> A C_ RR )
  assume ovolval3.m: |- M = { y e. RR* | E. f e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) ( A C_ U. ran ( (,) o. f ) /\ y = ( sum^ ` ( ( vol o. (,) ) o. f ) ) ) }

  disjoint A f
  disjoint A y
  disjoint f y
  disjoint f ph
  disjoint ph y
  disjoint f n
  disjoint k x
  assert |- ( ph -> ( vol* ` A ) = inf ( M , RR* , < ) )

  proof
    wph
    cA
    covol
    cfv
    cA
    cioo
    vf
    cv
    #
    ccom
    crn
    cuni
    wss
    #
    vy
    cv
    #
    cabs
    cmin
    ccom
    #
    @0
    ccom
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vf
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cn
    cmap
    co
    #
    wrex
    #
    vy
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cM
    cxr
    clt
    cinf
    #
    wph
    vy
    cA
    vf
    @12
    ovolval3.a
    @12
    eqid
    ovolval2
    @13
    @14
    wceq
    wph
    cxr
    @12
    cM
    clt
    cM
    @1
    @2
    cvol
    cioo
    ccom
    #
    @0
    ccom
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vf
    @10
    wrex
    #
    vy
    cxr
    crab
    @12
    ovolval3.m
    @20
    @11
    vy
    cxr
    @19
    @7
    vf
    @10
    @0
    @10
    wcel
    #
    @18
    @6
    @1
    @21
    @17
    @5
    @2
    @21
    @16
    @4
    csumge0
    @21
    vn
    cn
    vn
    cv
    #
    @0
    cfv
    #
    @15
    cfv
    #
    cmpt
    #
    vn
    cn
    @23
    @3
    cfv
    #
    cmpt
    #
    @16
    @4
    @21
    vn
    cn
    @24
    @26
    @21
    @22
    cn
    wcel
    #
    wa
    #
    @23
    cioo
    cfv
    #
    cvol
    cfv
    #
    @23
    c2nd
    cfv
    #
    @23
    c1st
    cfv
    #
    cmin
    co
    #
    @24
    @26
    @29
    @31
    @33
    @32
    cioo
    co
    #
    cvol
    cfv
    #
    @34
    @29
    @30
    @35
    cvol
    @29
    @30
    @33
    @32
    cop
    #
    cioo
    cfv
    #
    @35
    @29
    @23
    @37
    cioo
    @29
    @23
    @8
    wcel
    #
    @23
    @37
    wceq
    @21
    cn
    @8
    @22
    @0
    @21
    @0
    @8
    cn
    cmap
    co
    #
    wcel
    cn
    @8
    @0
    wf
    @10
    @40
    @0
    @8
    cvv
    wcel
    @9
    @8
    wss
    @10
    @40
    wss
    cr
    cr
    reex
    reex
    xpex
    cle
    @8
    inss2
    @9
    @8
    cn
    cvv
    mapss
    mp2an
    sseli
    @0
    @8
    cn
    elmapi
    syl
    #
    ffvelrnda
    #
    @23
    cr
    cr
    1st2nd2
    syl
    #
    fveq2d
    @38
    @35
    wceq
    @29
    @35
    @38
    @33
    @32
    cioo
    df-ov
    eqcomi
    a1i
    eqtrd
    fveq2d
    @29
    @33
    cr
    wcel
    #
    @32
    cr
    wcel
    #
    @33
    @32
    cle
    wbr
    #
    @36
    @34
    wceq
    @29
    @39
    @44
    @42
    @23
    cr
    cr
    xp1st
    syl
    #
    @29
    @39
    @45
    @42
    @23
    cr
    cr
    xp2nd
    syl
    #
    @29
    @44
    @45
    @46
    @29
    cn
    @9
    @0
    wf
    #
    @28
    @44
    @45
    @46
    w3a
    @21
    @49
    @28
    @0
    @9
    cn
    elmapi
    adantr
    @21
    @28
    simpr
    @0
    @22
    ovolfcl
    syl2anc
    simp3d
    #
    @33
    @32
    volioo
    syl3anc
    eqtrd
    @29
    cioo
    wfun
    #
    @23
    cioo
    cdm
    #
    wcel
    @24
    @31
    wceq
    @51
    @29
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    @51
    ioof
    @53
    @54
    cioo
    ffun
    ax-mp
    a1i
    @29
    @23
    @53
    @52
    @29
    @8
    @53
    @23
    rexpssxrxp
    @42
    sseldi
    @53
    @52
    wceq
    @29
    @52
    @53
    @53
    @54
    cioo
    ioof
    fdmi
    eqcomi
    a1i
    eleqtrd
    @23
    cvol
    cioo
    fvco
    syl2anc
    @29
    @26
    @37
    @3
    cfv
    #
    @33
    @32
    @3
    co
    #
    @34
    @29
    @23
    @37
    @3
    @43
    fveq2d
    @55
    @56
    wceq
    @29
    @56
    @55
    @33
    @32
    @3
    df-ov
    eqcomi
    a1i
    @29
    @56
    @33
    @32
    cmin
    co
    cabs
    cfv
    #
    @34
    cabs
    cfv
    #
    @34
    @29
    @33
    cc
    wcel
    #
    @32
    cc
    wcel
    #
    @56
    @57
    wceq
    @29
    @33
    @47
    recnd
    #
    @29
    @32
    @48
    recnd
    #
    @33
    @32
    @3
    @3
    eqid
    cnmetdval
    syl2anc
    @29
    @59
    @60
    @57
    @58
    wceq
    @61
    @62
    @33
    @32
    abssub
    syl2anc
    @29
    @33
    @32
    @47
    @48
    @50
    abssubge0d
    3eqtrd
    3eqtrd
    3eqtr4d
    mpteq2dva
    @21
    @53
    cc0
    cpnf
    cicc
    co
    #
    @15
    wf
    #
    cn
    @53
    @0
    wf
    @16
    @25
    wceq
    @64
    @21
    volioof
    a1i
    @21
    cn
    @8
    @53
    @0
    @41
    @8
    @53
    wss
    @21
    rexpssxrxp
    a1i
    fssd
    vn
    @15
    @0
    cn
    @53
    @63
    fcompt
    syl2anc
    @21
    cc
    cc
    cxp
    #
    cr
    @3
    wf
    #
    cn
    @65
    @0
    wf
    @4
    @27
    wceq
    @66
    @21
    cc
    cr
    cabs
    wf
    @65
    cc
    cmin
    wf
    @66
    absf
    subf
    @65
    cc
    cr
    cabs
    cmin
    fco
    mp2an
    a1i
    @21
    cn
    @8
    @65
    @0
    @41
    @8
    @65
    wss
    @21
    rr2sscn2
    a1i
    fssd
    vn
    @3
    @0
    cn
    @65
    cr
    fcompt
    syl2anc
    3eqtr4d
    fveq2d
    eqeq2d
    anbi2d
    rexbiia
    rabbii
    eqtr2i
    infeq1i
    a1i
    eqtrd
end
