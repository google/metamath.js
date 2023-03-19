include "ctotbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cme.mm"
include "cv.mm"
include "c1.mm"
include "cbl.mm"
include "co.mm"
include "ciun.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "cbnd.mm"
include "totbndmet.mm"
include "crp.mm"
include "wral.mm"
include "1rp.mm"
include "istotbnd3.mm"
include "simprbi.mm"
include "oveq2.mm"
include "iuneq2d.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "mpsyl.mm"
include "wa.mm"
include "caddc.mm"
include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wf.mm"
include "wss.mm"
include "simplll.mm"
include "elfpw.mm"
include "simplbi.mm"
include "ad2antrl.mm"
include "sselda.mm"
include "simpllr.mm"
include "metcl.mm"
include "syl3anc.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "metge0.mm"
include "ge0p1rpd.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "c0.mm"
include "wne.mm"
include "mptfi.mm"
include "rnfi.mm"
include "3syl.mm"
include "simplr.mm"
include "simprr.mm"
include "eleqtrrd.mm"
include "ne0i.mm"
include "cdm.mm"
include "dm0rn0.mm"
include "ovex.mm"
include "dmmpti.mm"
include "eqeq1i.mm"
include "iuneq1.mm"
include "sylbi.mm"
include "0iun.mm"
include "syl6eq.mm"
include "sylbir.mm"
include "necon3i.mm"
include "rpssre.mm"
include "syl6ss.mm"
include "wor.mm"
include "w3a.mm"
include "ltso.mm"
include "fisupcl.mm"
include "mpan.mm"
include "sseldd.mm"
include "cxmt.mm"
include "cmin.mm"
include "metxmet.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "1red.mm"
include "fimaxre2.mm"
include "syl2anc.mm"
include "cvv.mm"
include "elrnmpt1.mm"
include "mpan2.mm"
include "adantl.mm"
include "suprub.mm"
include "syl31anc.mm"
include "wb.mm"
include "leaddsub.mm"
include "mpbid.mm"
include "blss2.mm"
include "syl33anc.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfsup.mm"
include "nfov.mm"
include "nfss.mm"
include "nfv.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "cbvral.mm"
include "sylibr.mm"
include "iunss.mm"
include "eqsstr3d.mm"
include "cxr.mm"
include "rpxrd.mm"
include "blssm.mm"
include "eqssd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "rexlimdvaa.mm"
include "ralrimdva.mm"
include "isbnd.mm"
include "baib.mm"
include "sylibrd.mm"
include "sylc.mm"

theorem totbndbnd
  let cM: class M
  let cX: class X
  let vd: setvar d
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( M e. ( TotBnd ` X ) -> M e. ( Bnd ` X ) )

  proof
    cM
    cX
    ctotbnd
    cfv
    wcel
    #
    cM
    cX
    cme
    cfv
    wcel
    #
    vx
    vv
    cv
    #
    vx
    cv
    #
    c1
    cM
    cbl
    cfv
    #
    co
    #
    ciun
    #
    cX
    wceq
    #
    vv
    cX
    cpw
    cfn
    cin
    #
    wrex
    #
    cM
    cX
    cbnd
    cfv
    wcel
    #
    cM
    cX
    totbndmet
    c1
    crp
    wcel
    @0
    vx
    @2
    @3
    vd
    cv
    #
    @4
    co
    #
    ciun
    #
    cX
    wceq
    #
    vv
    @8
    wrex
    #
    vd
    crp
    wral
    #
    @9
    1rp
    @0
    @1
    @16
    vx
    vv
    cM
    cX
    vd
    istotbnd3
    simprbi
    @15
    @9
    vd
    c1
    crp
    @11
    c1
    wceq
    #
    @14
    @7
    vv
    @8
    @17
    @13
    @6
    cX
    @17
    vx
    @2
    @12
    @5
    @11
    c1
    @3
    @4
    oveq2
    iuneq2d
    eqeq1d
    rexbidv
    rspcv
    mpsyl
    @1
    @9
    cX
    vy
    cv
    #
    @11
    @4
    co
    #
    wceq
    #
    vd
    crp
    wrex
    #
    vy
    cX
    wral
    #
    @10
    @1
    @9
    @21
    vy
    cX
    @1
    @18
    cX
    wcel
    #
    wa
    #
    @7
    @21
    vv
    @8
    @24
    @2
    @8
    wcel
    #
    @7
    wa
    #
    wa
    #
    vz
    @2
    vz
    cv
    #
    @18
    cM
    co
    #
    c1
    caddc
    co
    #
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    crp
    wcel
    cX
    @18
    @33
    @4
    co
    #
    wceq
    #
    @21
    @27
    @32
    crp
    @33
    @27
    @2
    crp
    @31
    wf
    @32
    crp
    wss
    @27
    vz
    @2
    @30
    crp
    @31
    @27
    @28
    @2
    wcel
    #
    wa
    #
    @29
    @37
    @1
    @28
    cX
    wcel
    #
    @23
    @29
    cr
    wcel
    #
    @1
    @23
    @26
    @36
    simplll
    #
    @27
    @2
    cX
    @28
    @25
    @2
    cX
    wss
    #
    @24
    @7
    @25
    @41
    @2
    cfn
    wcel
    #
    @2
    cX
    elfpw
    #
    simplbi
    ad2antrl
    sselda
    #
    @1
    @23
    @26
    @36
    simpllr
    #
    @28
    @18
    cM
    cX
    metcl
    syl3anc
    #
    @37
    @1
    @38
    @23
    cc0
    @29
    cle
    wbr
    @40
    @44
    @45
    @28
    @18
    cM
    cX
    metge0
    syl3anc
    ge0p1rpd
    @31
    eqid
    #
    fmptd
    @2
    crp
    @31
    frn
    syl
    #
    @27
    @32
    cfn
    wcel
    #
    @32
    c0
    wne
    #
    @32
    cr
    wss
    #
    @33
    @32
    wcel
    #
    @25
    @49
    @24
    @7
    @25
    @42
    @31
    cfn
    wcel
    @49
    @25
    @41
    @42
    @43
    simprbi
    vz
    @2
    @30
    mptfi
    @31
    rnfi
    3syl
    ad2antrl
    #
    @27
    @18
    @6
    wcel
    @6
    c0
    wne
    @50
    @27
    @18
    cX
    @6
    @1
    @23
    @26
    simplr
    #
    @24
    @25
    @7
    simprr
    #
    eleqtrrd
    @6
    @18
    ne0i
    @32
    c0
    @6
    c0
    @32
    c0
    wceq
    @31
    cdm
    #
    c0
    wceq
    #
    @6
    c0
    wceq
    @31
    dm0rn0
    @57
    @6
    vx
    c0
    @5
    ciun
    #
    c0
    @57
    @2
    c0
    wceq
    @6
    @58
    wceq
    @56
    @2
    c0
    vz
    @2
    @30
    @31
    @29
    c1
    caddc
    ovex
    #
    @47
    dmmpti
    eqeq1i
    vx
    @2
    c0
    @5
    iuneq1
    sylbi
    vx
    @5
    0iun
    syl6eq
    sylbir
    necon3i
    3syl
    #
    @27
    @32
    crp
    cr
    @48
    rpssre
    syl6ss
    #
    cr
    clt
    wor
    @49
    @50
    @51
    w3a
    @52
    ltso
    cr
    @32
    clt
    fisupcl
    mpan
    syl3anc
    #
    sseldd
    #
    @27
    cX
    @34
    @27
    cX
    @6
    @34
    @55
    @27
    @5
    @34
    wss
    #
    vx
    @2
    wral
    #
    @6
    @34
    wss
    @27
    @28
    c1
    @4
    co
    #
    @34
    wss
    #
    vz
    @2
    wral
    @65
    @27
    @67
    vz
    @2
    @37
    cM
    cX
    cxmt
    cfv
    wcel
    #
    @38
    @23
    c1
    cr
    wcel
    #
    @33
    cr
    wcel
    #
    @29
    @33
    c1
    cmin
    co
    cle
    wbr
    #
    @67
    @27
    @68
    @36
    @1
    @68
    @23
    @26
    cM
    cX
    metxmet
    ad2antrr
    #
    adantr
    @44
    @45
    @37
    1red
    #
    @27
    @70
    @36
    @27
    @32
    cr
    @33
    @61
    @62
    sseldd
    adantr
    #
    @37
    @30
    @33
    cle
    wbr
    #
    @71
    @37
    @51
    @50
    vw
    cv
    @11
    cle
    wbr
    vw
    @32
    wral
    vd
    cr
    wrex
    #
    @30
    @32
    wcel
    #
    @75
    @27
    @51
    @36
    @61
    adantr
    #
    @27
    @50
    @36
    @60
    adantr
    @37
    @51
    @49
    @76
    @78
    @27
    @49
    @36
    @53
    adantr
    vd
    vw
    @32
    fimaxre2
    syl2anc
    @36
    @77
    @27
    @36
    @30
    cvv
    wcel
    @77
    @59
    vz
    @2
    @30
    @31
    cvv
    @47
    elrnmpt1
    mpan2
    adantl
    vd
    vw
    @32
    @30
    suprub
    syl31anc
    @37
    @39
    @69
    @70
    @75
    @71
    wb
    @46
    @73
    @74
    @29
    c1
    @33
    leaddsub
    syl3anc
    mpbid
    cM
    @28
    @18
    c1
    @33
    cX
    blss2
    syl33anc
    ralrimiva
    @64
    @67
    vx
    vz
    @2
    vz
    @5
    @34
    vz
    @5
    nfcv
    vz
    @18
    @33
    @4
    vz
    @18
    nfcv
    vz
    @4
    nfcv
    vz
    @32
    cr
    clt
    vz
    @31
    vz
    @2
    @30
    nfmpt1
    nfrn
    vz
    cr
    nfcv
    vz
    clt
    nfcv
    nfsup
    nfov
    nfss
    @67
    vx
    nfv
    @3
    @28
    wceq
    @5
    @66
    @34
    @3
    @28
    c1
    @4
    oveq1
    sseq1d
    cbvral
    sylibr
    vx
    @2
    @5
    @34
    iunss
    sylibr
    eqsstr3d
    @27
    @68
    @23
    @33
    cxr
    wcel
    @34
    cX
    wss
    @72
    @54
    @27
    @33
    @63
    rpxrd
    cM
    @18
    @33
    cX
    blssm
    syl3anc
    eqssd
    @20
    @35
    vd
    @33
    crp
    @11
    @33
    wceq
    @19
    @34
    cX
    @11
    @33
    @18
    @4
    oveq2
    eqeq2d
    rspcev
    syl2anc
    rexlimdvaa
    ralrimdva
    @10
    @1
    @22
    vy
    cM
    cX
    vd
    isbnd
    baib
    sylibrd
    sylc
end
