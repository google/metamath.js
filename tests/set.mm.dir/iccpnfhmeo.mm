include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cpnf.mm"
include "clt.mm"
include "wiso.mm"
include "cii.mm"
include "chmeo.mm"
include "wcel.mm"
include "wor.mm"
include "wpo.mm"
include "wfo.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "cxr.mm"
include "wss.mm"
include "iccssxr.mm"
include "xrltso.mm"
include "soss.mm"
include "mp2.mm"
include "sopo.mm"
include "ax-mp.mm"
include "wf1o.mm"
include "ccnv.mm"
include "wceq.mm"
include "caddc.mm"
include "cdiv.mm"
include "cif.mm"
include "cmpt.mm"
include "iccpnfcnv.mm"
include "simpli.mm"
include "f1ofo.mm"
include "wa.mm"
include "cmin.mm"
include "w3a.mm"
include "wne.mm"
include "cr.mm"
include "cle.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "1red.mm"
include "simp3.mm"
include "simp3bi.mm"
include "ltletrd.mm"
include "gtned.mm"
include "necomd.mm"
include "ifnefalse.mm"
include "syl.mm"
include "breq2.mm"
include "resubcl.mm"
include "sylancr.mm"
include "cc.mm"
include "wb.mm"
include "ax-1cn.mm"
include "recnd.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "redivcld.mm"
include "ltpnf.mm"
include "adantr.mm"
include "wn.mm"
include "cico.mm"
include "simpl3.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "eqid.mm"
include "icopnfhmeo.mm"
include "a1i.mm"
include "csn.mm"
include "cun.mm"
include "wo.mm"
include "simp1.mm"
include "0xr.mm"
include "rexri.mm"
include "0le1.mm"
include "snunico.mm"
include "mp3an.mm"
include "syl6eleqr.mm"
include "elun.mm"
include "sylib.mm"
include "ord.mm"
include "elsni.mm"
include "syl6.mm"
include "necon1ad.mm"
include "mpd.mm"
include "simp2.mm"
include "con1d.mm"
include "imp.mm"
include "isorel.mm"
include "syl12anc.mm"
include "mpbid.mm"
include "id.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "3brtr3d.mm"
include "ifbothda.mm"
include "eqbrtrd.mm"
include "3expia.mm"
include "eqeq1.mm"
include "ifbieq2d.mm"
include "pnfex.mm"
include "ifex.mm"
include "breqan12d.mm"
include "sylibrd.mm"
include "rgen2a.mm"
include "soisoi.mm"
include "mp4an.mm"
include "cxp.mm"
include "cin.mm"
include "cordt.mm"
include "cvv.mm"
include "ctsr.mm"
include "letsr.mm"
include "elexi.mm"
include "inex1.mm"
include "leiso.mm"
include "mp2an.mm"
include "mpbi.mm"
include "isores1.mm"
include "isores2.mm"
include "cdm.mm"
include "cps.mm"
include "tsrps.mm"
include "ledm.mm"
include "psssdm.mm"
include "eqcomi.mm"
include "ordthmeo.mm"
include "dfii5.mm"
include "ordtresticc.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "eleqtrri.mm"
include "pm3.2i.mm"

theorem iccpnfhmeo
  let vx: setvar x
  let cF: class F
  let cK: class K
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cG: class G
  let cJ: class J
  assume iccpnfhmeo.f: |- F = ( x e. ( 0 [,] 1 ) |-> if ( x = 1 , +oo , ( x / ( 1 - x ) ) ) )
  assume iccpnfhmeo.k: |- K = ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) )


  assert |- ( F Isom < , < ( ( 0 [,] 1 ) , ( 0 [,] +oo ) ) /\ F e. ( II Homeo K ) )

  proof
    cc0
    c1
    cicc
    co
    #
    cc0
    cpnf
    cicc
    co
    #
    clt
    clt
    cF
    wiso
    #
    cF
    cii
    cK
    chmeo
    co
    #
    wcel
    @0
    clt
    wor
    #
    @1
    clt
    wpo
    #
    @0
    @1
    cF
    wfo
    #
    vz
    cv
    #
    vw
    cv
    #
    clt
    wbr
    #
    @7
    cF
    cfv
    #
    @8
    cF
    cfv
    #
    clt
    wbr
    #
    wi
    #
    vw
    @0
    wral
    vz
    @0
    wral
    @2
    @0
    cxr
    wss
    #
    cxr
    clt
    wor
    #
    @4
    cc0
    c1
    iccssxr
    #
    xrltso
    @0
    cxr
    clt
    soss
    mp2
    @1
    clt
    wor
    #
    @5
    @1
    cxr
    wss
    #
    @15
    @17
    cc0
    cpnf
    iccssxr
    #
    xrltso
    @1
    cxr
    clt
    soss
    mp2
    @1
    clt
    sopo
    ax-mp
    @0
    @1
    cF
    wf1o
    #
    @6
    @20
    cF
    ccnv
    vy
    @1
    vy
    cv
    #
    cpnf
    wceq
    c1
    @21
    c1
    @21
    caddc
    co
    cdiv
    co
    cif
    cmpt
    wceq
    vx
    vy
    cF
    iccpnfhmeo.f
    iccpnfcnv
    simpli
    @0
    @1
    cF
    f1ofo
    ax-mp
    @13
    vz
    vw
    @0
    @7
    @0
    wcel
    #
    @8
    @0
    wcel
    #
    wa
    @9
    @7
    c1
    wceq
    #
    cpnf
    @7
    c1
    @7
    cmin
    co
    #
    cdiv
    co
    #
    cif
    #
    @8
    c1
    wceq
    #
    cpnf
    @8
    c1
    @8
    cmin
    co
    #
    cdiv
    co
    #
    cif
    #
    clt
    wbr
    #
    @12
    @22
    @23
    @9
    @32
    @22
    @23
    @9
    w3a
    #
    @27
    @26
    @31
    clt
    @33
    @7
    c1
    wne
    #
    @27
    @26
    wceq
    @33
    c1
    @7
    @33
    @7
    c1
    @22
    @23
    @7
    cr
    wcel
    #
    @9
    @22
    @35
    cc0
    @7
    cle
    wbr
    @7
    c1
    cle
    wbr
    cc0
    c1
    @7
    0re
    1re
    elicc2i
    simp1bi
    3ad2ant1
    #
    @33
    @7
    @8
    c1
    @36
    @23
    @22
    @8
    cr
    wcel
    #
    @9
    @23
    @37
    cc0
    @8
    cle
    wbr
    #
    @8
    c1
    cle
    wbr
    #
    cc0
    c1
    @8
    0re
    1re
    elicc2i
    #
    simp1bi
    3ad2ant2
    @33
    1red
    @22
    @23
    @9
    simp3
    @23
    @22
    @39
    @9
    @23
    @37
    @38
    @39
    @40
    simp3bi
    3ad2ant2
    ltletrd
    gtned
    #
    necomd
    #
    @7
    c1
    cpnf
    @26
    ifnefalse
    syl
    @28
    @26
    cpnf
    clt
    wbr
    #
    @26
    @30
    clt
    wbr
    @26
    @31
    clt
    wbr
    @33
    cpnf
    @30
    cpnf
    @31
    @26
    clt
    breq2
    @30
    @31
    @26
    clt
    breq2
    @33
    @43
    @28
    @33
    @26
    cr
    wcel
    @43
    @33
    @7
    @25
    @36
    @33
    c1
    cr
    wcel
    @35
    @25
    cr
    wcel
    1re
    @36
    c1
    @7
    resubcl
    sylancr
    @33
    @25
    cc0
    wne
    #
    c1
    @7
    wne
    #
    @41
    @33
    c1
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @44
    @45
    wb
    ax-1cn
    @33
    @7
    @36
    recnd
    @46
    @47
    wa
    @25
    cc0
    c1
    @7
    c1
    @7
    subeq0
    necon3bid
    sylancr
    mpbird
    redivcld
    @26
    ltpnf
    syl
    adantr
    @33
    @28
    wn
    #
    wa
    #
    @7
    vx
    cc0
    c1
    cico
    co
    #
    vx
    cv
    #
    c1
    @51
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cfv
    #
    @8
    @54
    cfv
    #
    @26
    @30
    clt
    @49
    @9
    @55
    @56
    clt
    wbr
    #
    @22
    @23
    @9
    @48
    simpl3
    @49
    @50
    cc0
    cpnf
    cico
    co
    #
    clt
    clt
    @54
    wiso
    #
    @7
    @50
    wcel
    #
    @8
    @50
    wcel
    #
    @9
    @57
    wb
    @59
    @49
    @59
    @54
    ccnfld
    ctopn
    cfv
    #
    @50
    crest
    co
    @62
    @58
    crest
    co
    chmeo
    co
    wcel
    vx
    @54
    @62
    @54
    eqid
    #
    @62
    eqid
    icopnfhmeo
    simpli
    a1i
    @33
    @60
    @48
    @33
    @34
    @60
    @42
    @33
    @60
    @7
    c1
    @33
    @60
    wn
    @7
    c1
    csn
    #
    wcel
    #
    @24
    @33
    @60
    @65
    @33
    @7
    @50
    @64
    cun
    #
    wcel
    @60
    @65
    wo
    @33
    @7
    @0
    @66
    @22
    @23
    @9
    simp1
    cc0
    cxr
    wcel
    c1
    cxr
    wcel
    cc0
    c1
    cle
    wbr
    @66
    @0
    wceq
    0xr
    c1
    1re
    rexri
    0le1
    cc0
    c1
    snunico
    mp3an
    #
    syl6eleqr
    @7
    @50
    @64
    elun
    sylib
    ord
    @7
    c1
    elsni
    syl6
    necon1ad
    mpd
    adantr
    #
    @33
    @48
    @61
    @33
    @61
    @28
    @33
    @61
    wn
    @8
    @64
    wcel
    #
    @28
    @33
    @61
    @69
    @33
    @8
    @66
    wcel
    @61
    @69
    wo
    @33
    @8
    @0
    @66
    @22
    @23
    @9
    simp2
    @67
    syl6eleqr
    @8
    @50
    @64
    elun
    sylib
    ord
    @8
    c1
    elsni
    syl6
    con1d
    imp
    #
    @50
    @58
    @7
    @8
    clt
    clt
    @54
    isorel
    syl12anc
    mpbid
    @49
    @60
    @55
    @26
    wceq
    @68
    vx
    @7
    @53
    @26
    @50
    @54
    @51
    @7
    wceq
    #
    @51
    @7
    @52
    @25
    cdiv
    @71
    id
    @51
    @7
    c1
    cmin
    oveq2
    oveq12d
    #
    @63
    @7
    @25
    cdiv
    ovex
    #
    fvmpt
    syl
    @49
    @61
    @56
    @30
    wceq
    @70
    vx
    @8
    @53
    @30
    @50
    @54
    @51
    @8
    wceq
    #
    @51
    @8
    @52
    @29
    cdiv
    @74
    id
    @51
    @8
    c1
    cmin
    oveq2
    oveq12d
    #
    @63
    @8
    @29
    cdiv
    ovex
    #
    fvmpt
    syl
    3brtr3d
    ifbothda
    eqbrtrd
    3expia
    @22
    @23
    @10
    @27
    @11
    @31
    clt
    vx
    @7
    @51
    c1
    wceq
    #
    cpnf
    @53
    cif
    #
    @27
    @0
    cF
    @71
    @77
    @24
    @53
    @26
    cpnf
    @51
    @7
    c1
    eqeq1
    @72
    ifbieq2d
    iccpnfhmeo.f
    @24
    cpnf
    @26
    pnfex
    @73
    ifex
    fvmpt
    vx
    @8
    @78
    @31
    @0
    cF
    @74
    @77
    @28
    @53
    @30
    cpnf
    @51
    @8
    c1
    eqeq1
    @75
    ifbieq2d
    iccpnfhmeo.f
    @28
    cpnf
    @30
    pnfex
    @76
    ifex
    fvmpt
    breqan12d
    sylibrd
    rgen2a
    vz
    vw
    @0
    @1
    clt
    clt
    cF
    soisoi
    mp4an
    #
    cF
    cle
    @0
    @0
    cxp
    #
    cin
    #
    cordt
    cfv
    #
    cle
    @1
    @1
    cxp
    #
    cin
    #
    cordt
    cfv
    #
    chmeo
    co
    #
    @3
    @81
    cvv
    wcel
    @84
    cvv
    wcel
    @0
    @1
    @81
    @84
    cF
    wiso
    #
    cF
    @86
    wcel
    cle
    @80
    cle
    ctsr
    letsr
    elexi
    #
    inex1
    cle
    @83
    @88
    inex1
    @0
    @1
    @81
    cle
    cF
    wiso
    #
    @87
    @0
    @1
    cle
    cle
    cF
    wiso
    #
    @89
    @2
    @90
    @79
    @14
    @18
    @2
    @90
    wb
    @16
    @19
    @0
    @1
    cF
    leiso
    mp2an
    mpbi
    @0
    @1
    cle
    cle
    cF
    isores1
    mpbi
    @0
    @1
    @81
    cle
    cF
    isores2
    mpbi
    @81
    @84
    cF
    cvv
    cvv
    @0
    @1
    @81
    cdm
    #
    @0
    cle
    cps
    wcel
    #
    @14
    @91
    @0
    wceq
    cle
    ctsr
    wcel
    @92
    letsr
    cle
    tsrps
    ax-mp
    #
    @16
    @0
    cle
    cxr
    ledm
    psssdm
    mp2an
    eqcomi
    @84
    cdm
    #
    @1
    @92
    @18
    @94
    @1
    wceq
    @93
    @19
    @1
    cle
    cxr
    ledm
    psssdm
    mp2an
    eqcomi
    ordthmeo
    mp3an
    cii
    @82
    cK
    @85
    chmeo
    dfii5
    cK
    cle
    cordt
    cfv
    @1
    crest
    co
    @85
    iccpnfhmeo.k
    cc0
    cpnf
    ordtresticc
    eqtri
    oveq12i
    eleqtrri
    pm3.2i
end
