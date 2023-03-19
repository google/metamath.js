include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cpnf.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cn.mm"
include "cr.mm"
include "wcel.mm"
include "adantr.mm"
include "cc0.mm"
include "cicc.mm"
include "wf.mm"
include "cxr.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "rpxrd.mm"
include "rpge0d.mm"
include "rpred.mm"
include "ltpnf.mm"
include "syl.mm"
include "xrltled.mm"
include "eliccxrd.mm"
include "eqid.mm"
include "fmptd.mm"
include "sge0xrcl.mm"
include "simpr.mm"
include "xrgtned.mm"
include "necomd.mm"
include "neneqd.mm"
include "sge0repnf.mm"
include "mpbird.mm"
include "wne.mm"
include "rpne0d.mm"
include "redivcld.mm"
include "arch.mm"
include "w3a.mm"
include "wex.mm"
include "chash.mm"
include "wral.mm"
include "ishashinf.mm"
include "r19.21bi.mm"
include "df-rex.mm"
include "sylib.mm"
include "adantlr.mm"
include "3adant3.mm"
include "nfv.mm"
include "simprl.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "cn0.mm"
include "nnnn0.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "hashclb.mm"
include "adantrl.mm"
include "3ad2antl2.mm"
include "elind.mm"
include "cmul.mm"
include "simp3.mm"
include "3ad2ant1.mm"
include "nnre.mm"
include "3ad2ant2.mm"
include "crp.mm"
include "ltdivmul2d.mm"
include "mpbid.mm"
include "csu.mm"
include "adantll.mm"
include "ad3antrrr.mm"
include "cle.mm"
include "elicod.mm"
include "sge0fsummpt.mm"
include "cc.mm"
include "recnd.mm"
include "ad2antrr.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "adantl.mm"
include "3eqtrrd.mm"
include "adantllr.mm"
include "3adantl3.mm"
include "breqtrd.mm"
include "jca.mm"
include "ex.mm"
include "eximd.mm"
include "mpd.mm"
include "sylibr.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "wss.mm"
include "elpwinss.mm"
include "sge0lessmpt.mm"
include "xrlenltd.mm"
include "ralrimiva.mm"
include "ralnex.mm"
include "pm2.65da.mm"
include "nltpnft.mm"

theorem sge0rpcpnf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vn: setvar n
  let vy: setvar y
  let vk: setvar k
  assume sge0rpcpnf.a: |- ( ph -> A e. V )
  assume sge0rpcpnf.nfi: |- ( ph -> -. A e. Fin )
  assume sge0rpcpnf.b: |- ( ph -> B e. RR+ )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint A n
  disjoint A y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint B n
  disjoint B y
  disjoint n ph
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( x e. A |-> B ) ) = +oo )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    csumge0
    cfv
    #
    cpnf
    wceq
    #
    @1
    cpnf
    clt
    wbr
    #
    wn
    #
    wph
    @3
    @1
    vx
    vy
    cv
    #
    cB
    cmpt
    #
    csumge0
    cfv
    #
    clt
    wbr
    #
    vy
    cA
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wph
    @3
    wa
    #
    @1
    cB
    cdiv
    co
    #
    vn
    cv
    #
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    @11
    @12
    @13
    cr
    wcel
    @16
    @12
    @1
    cB
    @12
    @1
    cr
    wcel
    #
    @2
    wn
    @12
    @1
    cpnf
    @12
    cpnf
    @1
    @12
    @1
    cpnf
    @12
    @0
    cV
    cA
    wph
    cA
    cV
    wcel
    #
    @3
    sge0rpcpnf.a
    adantr
    #
    wph
    cA
    cc0
    cpnf
    cicc
    co
    #
    @0
    wf
    @3
    wph
    vx
    cA
    cB
    @20
    @0
    wph
    cB
    @20
    wcel
    #
    vx
    cv
    #
    cA
    wcel
    #
    wph
    cc0
    cpnf
    cB
    cc0
    cxr
    wcel
    #
    wph
    0xr
    a1i
    cpnf
    cxr
    wcel
    #
    wph
    pnfxr
    a1i
    #
    wph
    cB
    sge0rpcpnf.b
    rpxrd
    #
    wph
    cB
    sge0rpcpnf.b
    rpge0d
    #
    wph
    cB
    cpnf
    @27
    @26
    wph
    cB
    cr
    wcel
    #
    cB
    cpnf
    clt
    wbr
    #
    wph
    cB
    sge0rpcpnf.b
    rpred
    #
    cB
    ltpnf
    syl
    #
    xrltled
    eliccxrd
    #
    adantr
    #
    @0
    eqid
    fmptd
    #
    adantr
    #
    sge0xrcl
    @25
    @12
    pnfxr
    a1i
    wph
    @3
    simpr
    xrgtned
    necomd
    neneqd
    @12
    @0
    cV
    cA
    @19
    @36
    sge0repnf
    mpbird
    #
    wph
    @29
    @3
    @31
    adantr
    wph
    cB
    cc0
    wne
    @3
    wph
    cB
    sge0rpcpnf.b
    rpne0d
    adantr
    redivcld
    @13
    vn
    arch
    syl
    @12
    @15
    @11
    vn
    cn
    @12
    @14
    cn
    wcel
    #
    @15
    @11
    @12
    @38
    @15
    w3a
    #
    @5
    @10
    wcel
    #
    @8
    wa
    #
    vy
    wex
    #
    @11
    @39
    @5
    @9
    wcel
    #
    @5
    chash
    cfv
    #
    @14
    wceq
    #
    wa
    #
    vy
    wex
    #
    @42
    @12
    @38
    @47
    @15
    wph
    @38
    @47
    @3
    wph
    @38
    wa
    #
    @45
    vy
    @9
    wrex
    #
    @47
    wph
    @49
    vn
    cn
    wph
    cA
    cfn
    wcel
    wn
    @49
    vn
    cn
    wral
    sge0rpcpnf.nfi
    vy
    cA
    vn
    ishashinf
    syl
    r19.21bi
    @45
    vy
    @9
    df-rex
    sylib
    adantlr
    3adant3
    @39
    @46
    @41
    vy
    @39
    vy
    nfv
    @39
    @46
    @41
    @39
    @46
    wa
    #
    @40
    @8
    @50
    @9
    cfn
    @5
    @39
    @43
    @45
    simprl
    @38
    @12
    @46
    @5
    cfn
    wcel
    #
    @15
    @38
    @45
    @51
    @43
    @38
    @45
    wa
    #
    @44
    cn
    wcel
    #
    @51
    @52
    @44
    @14
    cn
    @38
    @45
    simpr
    @38
    @45
    simpl
    eqeltrd
    @53
    @51
    @44
    cn0
    wcel
    #
    @44
    nnnn0
    @53
    @5
    cvv
    wcel
    #
    @51
    @54
    wb
    @55
    @53
    vy
    vex
    a1i
    @5
    cvv
    hashclb
    syl
    mpbird
    syl
    adantrl
    #
    3ad2antl2
    elind
    @50
    @1
    @14
    cB
    cmul
    co
    #
    @7
    clt
    @39
    @1
    @57
    clt
    wbr
    #
    @46
    @39
    @15
    @58
    @12
    @38
    @15
    simp3
    @39
    @1
    @14
    cB
    @12
    @38
    @17
    @15
    @37
    3ad2ant1
    @38
    @12
    @14
    cr
    wcel
    @15
    @14
    nnre
    3ad2ant2
    @12
    @38
    cB
    crp
    wcel
    #
    @15
    wph
    @59
    @3
    sge0rpcpnf.b
    adantr
    3ad2ant1
    ltdivmul2d
    mpbid
    adantr
    @12
    @38
    @46
    @57
    @7
    wceq
    #
    @15
    wph
    @38
    @46
    @60
    @3
    @48
    @46
    wa
    #
    @7
    @5
    cB
    vx
    csu
    #
    @44
    cB
    cmul
    co
    #
    @57
    @61
    @5
    cB
    vx
    @38
    @46
    @51
    wph
    @56
    adantll
    #
    @61
    @22
    @5
    wcel
    #
    wa
    #
    cc0
    cpnf
    cB
    @24
    @66
    0xr
    a1i
    @25
    @66
    pnfxr
    a1i
    wph
    cB
    cxr
    wcel
    @38
    @46
    @65
    @27
    ad3antrrr
    wph
    cc0
    cB
    cle
    wbr
    @38
    @46
    @65
    @28
    ad3antrrr
    wph
    @30
    @38
    @46
    @65
    @32
    ad3antrrr
    elicod
    sge0fsummpt
    @61
    @51
    cB
    cc
    wcel
    #
    @62
    @63
    wceq
    @64
    wph
    @67
    @38
    @46
    wph
    cB
    @31
    recnd
    ad2antrr
    @5
    cB
    vx
    fsumconst
    syl2anc
    @46
    @63
    @57
    wceq
    #
    @48
    @45
    @68
    @43
    @44
    @14
    cB
    cmul
    oveq1
    adantl
    adantl
    3eqtrrd
    adantllr
    3adantl3
    breqtrd
    jca
    ex
    eximd
    mpd
    @8
    vy
    @10
    df-rex
    sylibr
    3exp
    rexlimdv
    mpd
    wph
    @11
    wn
    #
    @3
    wph
    @8
    wn
    #
    vy
    @10
    wral
    @69
    wph
    @70
    vy
    @10
    wph
    @40
    wa
    #
    @7
    @1
    cle
    wbr
    @70
    @71
    vx
    cA
    cB
    @5
    cV
    wph
    @18
    @40
    sge0rpcpnf.a
    adantr
    wph
    @23
    @21
    @40
    @34
    adantlr
    @40
    @5
    cA
    wss
    wph
    @5
    cA
    cfn
    elpwinss
    adantl
    sge0lessmpt
    @71
    @7
    @1
    @71
    @6
    @10
    @5
    wph
    @40
    simpr
    wph
    @5
    @20
    @6
    wf
    @40
    wph
    vx
    @5
    cB
    @20
    @6
    wph
    @21
    @65
    @33
    adantr
    @6
    eqid
    fmptd
    adantr
    sge0xrcl
    wph
    @1
    cxr
    wcel
    #
    @40
    wph
    @0
    cV
    cA
    sge0rpcpnf.a
    @35
    sge0xrcl
    #
    adantr
    xrlenltd
    mpbid
    ralrimiva
    @8
    vy
    @10
    ralnex
    sylib
    adantr
    pm2.65da
    wph
    @72
    @2
    @4
    wb
    @73
    @1
    nltpnft
    syl
    mpbird
end
