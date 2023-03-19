include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cicc.mm"
include "co.mm"
include "cin.mm"
include "wss.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "crest.mm"
include "csconn.mm"
include "w3a.mm"
include "wrex.mm"
include "wral.mm"
include "clly.mm"
include "simprl.mm"
include "inss1.mm"
include "simprr.mm"
include "sseldi.mm"
include "tg2.mm"
include "syl2anc.mm"
include "wceq.mm"
include "cxr.mm"
include "wi.mm"
include "cxp.mm"
include "cpw.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ioof.mm"
include "ffn.mm"
include "ovelrn.mm"
include "mp2b.mm"
include "simprrr.mm"
include "syl5ss.mm"
include "simprrl.mm"
include "ineq1d.mm"
include "oveq2d.mm"
include "ioosconn.mm"
include "ioossre.mm"
include "cconn.mm"
include "eqid.mm"
include "resconn.mm"
include "reconn.mm"
include "bitrd.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "ssralv.mm"
include "ralimdv.mm"
include "syld.mm"
include "mp1i.mm"
include "inss2.mm"
include "iccconn.mm"
include "iccssre.mm"
include "syl.mm"
include "mpbid.mm"
include "ad2antrr.mm"
include "mpsyl.mm"
include "ssin.mm"
include "2ralbii.mm"
include "r19.26-2.mm"
include "bitr3i.mm"
include "sylanbrc.mm"
include "sstri.mm"
include "sylibr.mm"
include "eqeltrd.mm"
include "3jca.mm"
include "exp32.mm"
include "rexlimdvw.mm"
include "syl5bi.mm"
include "reximdvai.mm"
include "ctb.mm"
include "retopbas.mm"
include "bastg.mm"
include "ssrexv.mm"
include "syl6.mm"
include "mpd.mm"
include "ralrimivva.mm"
include "ctop.mm"
include "cvv.mm"
include "retop.mm"
include "ovex.mm"
include "subislly.mm"
include "mp2an.mm"

theorem iccllysconn
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( topGen ` ran (,) ) |`t ( A [,] B ) ) e. Locally SConn )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
    #
    vz
    cv
    #
    cA
    cB
    cicc
    co
    #
    cin
    #
    vx
    cv
    #
    wss
    #
    vy
    cv
    #
    @1
    wcel
    #
    cioo
    crn
    #
    ctg
    cfv
    #
    @3
    crest
    co
    #
    csconn
    wcel
    #
    w3a
    #
    vz
    @9
    wrex
    #
    vy
    @4
    @2
    cin
    #
    wral
    vx
    @9
    wral
    #
    @9
    @2
    crest
    co
    #
    csconn
    clly
    wcel
    #
    @0
    @13
    vx
    vy
    @9
    @14
    @0
    @4
    @9
    wcel
    #
    @6
    @14
    wcel
    #
    wa
    #
    wa
    #
    @7
    @1
    @4
    wss
    #
    wa
    #
    vz
    @8
    wrex
    #
    @13
    @21
    @18
    @6
    @4
    wcel
    @24
    @0
    @18
    @19
    simprl
    @21
    @14
    @4
    @6
    @4
    @2
    inss1
    @0
    @18
    @19
    simprr
    sseldi
    vz
    @4
    @8
    @6
    tg2
    syl2anc
    @21
    @24
    @12
    vz
    @8
    wrex
    #
    @13
    @21
    @23
    @12
    vz
    @8
    @1
    @8
    wcel
    #
    @1
    va
    cv
    #
    vb
    cv
    #
    cioo
    co
    #
    wceq
    #
    vb
    cxr
    wrex
    #
    va
    cxr
    wrex
    #
    @21
    @23
    @12
    wi
    #
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    cioo
    @34
    wfn
    @26
    @32
    wb
    ioof
    @34
    @35
    cioo
    ffn
    va
    vb
    cxr
    cxr
    @1
    cioo
    ovelrn
    mp2b
    @21
    @31
    @33
    va
    cxr
    @21
    @30
    @33
    vb
    cxr
    @21
    @30
    @23
    @12
    @21
    @30
    @23
    wa
    #
    wa
    #
    @5
    @7
    @11
    @37
    @3
    @1
    @4
    @1
    @2
    inss1
    @21
    @30
    @7
    @22
    simprrr
    syl5ss
    @21
    @30
    @7
    @22
    simprrl
    @37
    @10
    @9
    @29
    @2
    cin
    #
    crest
    co
    #
    csconn
    @37
    @3
    @38
    @9
    crest
    @37
    @1
    @29
    @2
    @21
    @30
    @23
    simprl
    ineq1d
    oveq2d
    @37
    vu
    cv
    vv
    cv
    cicc
    co
    #
    @38
    wss
    #
    vv
    @38
    wral
    vu
    @38
    wral
    #
    @39
    csconn
    wcel
    #
    @37
    @40
    @29
    wss
    #
    vv
    @38
    wral
    #
    vu
    @38
    wral
    #
    @40
    @2
    wss
    #
    vv
    @38
    wral
    #
    vu
    @38
    wral
    #
    @42
    @44
    vv
    @29
    wral
    #
    vu
    @29
    wral
    #
    @46
    @37
    @9
    @29
    crest
    co
    #
    csconn
    wcel
    #
    @51
    @27
    @28
    ioosconn
    @29
    cr
    wss
    #
    @53
    @51
    wb
    @27
    @28
    ioossre
    #
    @54
    @53
    @52
    cconn
    wcel
    @51
    @29
    @52
    @52
    eqid
    resconn
    vu
    vv
    @29
    reconn
    bitrd
    ax-mp
    mpbi
    @38
    @29
    wss
    #
    @51
    @46
    wi
    @29
    @2
    inss1
    #
    @56
    @51
    @45
    vu
    @29
    wral
    @46
    @56
    @50
    @45
    vu
    @29
    @44
    vv
    @38
    @29
    ssralv
    ralimdv
    @45
    vu
    @38
    @29
    ssralv
    syld
    ax-mp
    mp1i
    @38
    @2
    wss
    #
    @37
    @47
    vv
    @2
    wral
    #
    vu
    @2
    wral
    #
    @49
    @29
    @2
    inss2
    @0
    @60
    @20
    @36
    @0
    @16
    cconn
    wcel
    #
    @60
    cA
    cB
    iccconn
    @0
    @2
    cr
    wss
    @61
    @60
    wb
    cA
    cB
    iccssre
    vu
    vv
    @2
    reconn
    syl
    mpbid
    ad2antrr
    @58
    @60
    @48
    vu
    @2
    wral
    @49
    @58
    @59
    @48
    vu
    @2
    @47
    vv
    @38
    @2
    ssralv
    ralimdv
    @48
    vu
    @38
    @2
    ssralv
    syld
    mpsyl
    @42
    @44
    @47
    wa
    #
    vv
    @38
    wral
    vu
    @38
    wral
    @46
    @49
    wa
    @62
    @41
    vu
    vv
    @38
    @38
    @40
    @29
    @2
    ssin
    2ralbii
    @44
    @47
    vu
    vv
    @38
    @38
    r19.26-2
    bitr3i
    sylanbrc
    @38
    cr
    wss
    #
    @43
    @42
    wb
    @38
    @29
    cr
    @57
    @55
    sstri
    @63
    @43
    @39
    cconn
    wcel
    @42
    @38
    @39
    @39
    eqid
    resconn
    vu
    vv
    @38
    reconn
    bitrd
    ax-mp
    sylibr
    eqeltrd
    3jca
    exp32
    rexlimdvw
    rexlimdvw
    syl5bi
    reximdvai
    @8
    ctb
    wcel
    @8
    @9
    wss
    @25
    @13
    wi
    retopbas
    @8
    ctb
    bastg
    @12
    vz
    @8
    @9
    ssrexv
    mp2b
    syl6
    mpd
    ralrimivva
    @9
    ctop
    wcel
    @2
    cvv
    wcel
    @17
    @15
    wb
    retop
    cA
    cB
    cicc
    ovex
    vx
    vy
    vz
    csconn
    @2
    @9
    cvv
    subislly
    mp2an
    sylibr
end
