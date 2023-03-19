include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "crn.mm"
include "cfi.mm"
include "ctg.mm"
include "cxr.mm"
include "cv.mm"
include "cpnf.mm"
include "cioc.mm"
include "co.mm"
include "cmpt.mm"
include "cmnf.mm"
include "cico.mm"
include "cun.mm"
include "eqid.mm"
include "leordtval2.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "fvex.mm"
include "cicc.mm"
include "wf.mm"
include "cdif.mm"
include "wceq.mm"
include "wrex.mm"
include "cxp.mm"
include "wfn.mm"
include "wb.mm"
include "cpw.mm"
include "iccf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "ovelrn.mm"
include "difeq2.mm"
include "ccld.mm"
include "iccordt.mm"
include "letopuni.mm"
include "cldopn.mm"
include "syl6eqel.mm"
include "rexlimivw.mm"
include "sylbi.mm"
include "fmpti.mm"
include "frn.mm"
include "ssexi.mm"
include "mnfxr.mm"
include "fnovrn.mm"
include "mp3an12.mm"
include "wbr.mm"
include "a1i.mm"
include "id.mm"
include "pnfxr.mm"
include "mnfle.mm"
include "pnfge.mm"
include "clt.mm"
include "df-icc.mm"
include "df-ioc.mm"
include "xrltnle.mm"
include "xrletr.mm"
include "w3a.mm"
include "wa.mm"
include "xrlelttr.mm"
include "wi.mm"
include "xrltle.mm"
include "3adant2.mm"
include "syld.mm"
include "ixxun.mm"
include "syl32anc.mm"
include "iccmax.mm"
include "syl6eq.mm"
include "cin.mm"
include "c0.mm"
include "iccssxr.mm"
include "ixxdisj.mm"
include "mp3an13.mm"
include "uneqdifeq.mm"
include "sylancr.mm"
include "mpbid.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "xrex.mm"
include "difexg.mm"
include "elrnmpti.mm"
include "sylibr.mm"
include "df-ico.mm"
include "xrlenlt.mm"
include "xrltletr.mm"
include "uncom.mm"
include "3eqtr3g.mm"
include "incom.mm"
include "syl5eq.mm"
include "unssi.mm"
include "fiss.mm"
include "mp2an.mm"
include "tgss.mm"
include "eqsstri.mm"
include "ctop.mm"
include "letop.mm"
include "tgfiss.mm"
include "eqssi.mm"

theorem lecldbas
  let vx: setvar x
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vy: setvar y
  let vz: setvar z
  assume lecldbas.1: |- F = ( x e. ran [,] |-> ( RR* \ x ) )


  assert |- ( ordTop ` <_ ) = ( topGen ` ( fi ` ran F ) )

  proof
    cle
    cordt
    cfv
    #
    cF
    crn
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    @0
    vy
    cxr
    vy
    cv
    #
    cpnf
    cioc
    co
    #
    cmpt
    #
    crn
    #
    vy
    cxr
    cmnf
    @4
    cico
    co
    #
    cmpt
    #
    crn
    #
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    @3
    vy
    @7
    @10
    @7
    eqid
    @10
    eqid
    leordtval2
    @2
    cvv
    wcel
    @12
    @2
    wss
    #
    @13
    @3
    wss
    @1
    cfi
    fvex
    @1
    cvv
    wcel
    @11
    @1
    wss
    @14
    @1
    @0
    cle
    cordt
    fvex
    cicc
    crn
    #
    @0
    cF
    wf
    @1
    @0
    wss
    #
    vx
    @15
    @0
    cxr
    vx
    cv
    #
    cdif
    #
    cF
    lecldbas.1
    @17
    @15
    wcel
    #
    @17
    va
    cv
    #
    vb
    cv
    #
    cicc
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
    @18
    @0
    wcel
    #
    cicc
    cxr
    cxr
    cxp
    #
    wfn
    #
    @19
    @25
    wb
    @27
    cxr
    cpw
    #
    cicc
    wf
    @28
    iccf
    @27
    @29
    cicc
    ffn
    ax-mp
    #
    va
    vb
    cxr
    cxr
    @17
    cicc
    ovelrn
    ax-mp
    @24
    @26
    va
    cxr
    @23
    @26
    vb
    cxr
    @23
    @18
    cxr
    @22
    cdif
    #
    @0
    @17
    @22
    cxr
    difeq2
    @22
    @0
    ccld
    cfv
    wcel
    @31
    @0
    wcel
    @20
    @21
    iccordt
    @22
    @0
    cxr
    letopuni
    cldopn
    ax-mp
    syl6eqel
    rexlimivw
    rexlimivw
    sylbi
    fmpti
    @15
    @0
    cF
    frn
    ax-mp
    #
    ssexi
    @7
    @10
    @1
    cxr
    @1
    @6
    wf
    @7
    @1
    wss
    vy
    cxr
    @1
    @5
    @6
    @6
    eqid
    @4
    cxr
    wcel
    #
    @5
    @18
    wceq
    #
    vx
    @15
    wrex
    #
    @5
    @1
    wcel
    @33
    cmnf
    @4
    cicc
    co
    #
    @15
    wcel
    #
    @5
    cxr
    @36
    cdif
    #
    wceq
    #
    @35
    @28
    cmnf
    cxr
    wcel
    #
    @33
    @37
    @30
    mnfxr
    cxr
    cxr
    cmnf
    @4
    cicc
    fnovrn
    mp3an12
    @33
    @38
    @5
    @33
    @36
    @5
    cun
    #
    cxr
    wceq
    #
    @38
    @5
    wceq
    #
    @33
    @41
    cmnf
    cpnf
    cicc
    co
    #
    cxr
    @33
    @40
    @33
    cpnf
    cxr
    wcel
    #
    cmnf
    @4
    cle
    wbr
    #
    @4
    cpnf
    cle
    wbr
    #
    @41
    @44
    wceq
    @40
    @33
    mnfxr
    a1i
    #
    @33
    id
    #
    @45
    @33
    pnfxr
    a1i
    #
    @4
    mnfle
    #
    @4
    pnfge
    #
    va
    vb
    vc
    vz
    cmnf
    @4
    cpnf
    cioc
    cicc
    cle
    cle
    clt
    cle
    cicc
    cle
    cle
    va
    vb
    vc
    df-icc
    #
    va
    vb
    vc
    df-ioc
    #
    @4
    vz
    cv
    #
    xrltnle
    #
    @53
    @55
    @4
    cpnf
    xrletr
    @40
    @33
    @55
    cxr
    wcel
    #
    w3a
    @46
    @4
    @55
    clt
    wbr
    wa
    cmnf
    @55
    clt
    wbr
    #
    cmnf
    @55
    cle
    wbr
    #
    cmnf
    @4
    @55
    xrlelttr
    @40
    @57
    @58
    @59
    wi
    @33
    cmnf
    @55
    xrltle
    3adant2
    syld
    ixxun
    syl32anc
    iccmax
    syl6eq
    @33
    @36
    cxr
    wss
    @36
    @5
    cin
    c0
    wceq
    #
    @42
    @43
    wb
    cmnf
    @4
    iccssxr
    @40
    @33
    @45
    @60
    mnfxr
    pnfxr
    va
    vb
    vc
    vz
    cmnf
    @4
    cpnf
    cioc
    cle
    cle
    clt
    cle
    cicc
    @53
    @54
    @56
    ixxdisj
    mp3an13
    @36
    @5
    cxr
    uneqdifeq
    sylancr
    mpbid
    eqcomd
    @34
    @39
    vx
    @36
    @15
    @17
    @36
    wceq
    @18
    @38
    @5
    @17
    @36
    cxr
    difeq2
    eqeq2d
    rspcev
    syl2anc
    vx
    @15
    @18
    @5
    cF
    lecldbas.1
    cxr
    cvv
    wcel
    @18
    cvv
    wcel
    xrex
    cxr
    @17
    cvv
    difexg
    ax-mp
    #
    elrnmpti
    sylibr
    fmpti
    cxr
    @1
    @6
    frn
    ax-mp
    cxr
    @1
    @9
    wf
    @10
    @1
    wss
    vy
    cxr
    @1
    @8
    @9
    @9
    eqid
    @33
    @8
    @18
    wceq
    #
    vx
    @15
    wrex
    #
    @8
    @1
    wcel
    @33
    @4
    cpnf
    cicc
    co
    #
    @15
    wcel
    #
    @8
    cxr
    @64
    cdif
    #
    wceq
    #
    @63
    @28
    @33
    @45
    @65
    @30
    pnfxr
    cxr
    cxr
    @4
    cpnf
    cicc
    fnovrn
    mp3an13
    @33
    @66
    @8
    @33
    @64
    @8
    cun
    #
    cxr
    wceq
    #
    @66
    @8
    wceq
    #
    @33
    @8
    @64
    cun
    #
    @44
    @68
    cxr
    @33
    @40
    @33
    @45
    @46
    @47
    @71
    @44
    wceq
    @48
    @49
    @50
    @51
    @52
    va
    vb
    vc
    vz
    cmnf
    @4
    cpnf
    cicc
    cicc
    cle
    clt
    cle
    cle
    cico
    cle
    cle
    va
    vb
    vc
    df-ico
    #
    @53
    @4
    @55
    xrlenlt
    #
    @53
    @57
    @33
    @45
    w3a
    @55
    @4
    clt
    wbr
    @47
    wa
    @55
    cpnf
    clt
    wbr
    #
    @55
    cpnf
    cle
    wbr
    #
    @55
    @4
    cpnf
    xrltletr
    @57
    @45
    @74
    @75
    wi
    @33
    @55
    cpnf
    xrltle
    3adant2
    syld
    cmnf
    @4
    @55
    xrletr
    ixxun
    syl32anc
    @8
    @64
    uncom
    iccmax
    3eqtr3g
    @33
    @64
    cxr
    wss
    @64
    @8
    cin
    #
    c0
    wceq
    @69
    @70
    wb
    @4
    cpnf
    iccssxr
    @33
    @76
    @8
    @64
    cin
    #
    c0
    @64
    @8
    incom
    @40
    @33
    @45
    @77
    c0
    wceq
    mnfxr
    pnfxr
    va
    vb
    vc
    vz
    cmnf
    @4
    cpnf
    cicc
    cle
    clt
    cle
    cle
    cico
    @72
    @53
    @73
    ixxdisj
    mp3an13
    syl5eq
    @64
    @8
    cxr
    uneqdifeq
    sylancr
    mpbid
    eqcomd
    @62
    @67
    vx
    @64
    @15
    @17
    @64
    wceq
    @18
    @66
    @8
    @17
    @64
    cxr
    difeq2
    eqeq2d
    rspcev
    syl2anc
    vx
    @15
    @18
    @8
    cF
    lecldbas.1
    @61
    elrnmpti
    sylibr
    fmpti
    cxr
    @1
    @9
    frn
    ax-mp
    unssi
    @11
    @1
    cvv
    fiss
    mp2an
    @12
    @2
    cvv
    tgss
    mp2an
    eqsstri
    @0
    ctop
    wcel
    @16
    @3
    @0
    wss
    letop
    @32
    @1
    @0
    tgfiss
    mp2an
    eqssi
end
