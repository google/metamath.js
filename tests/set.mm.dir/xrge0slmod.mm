include "cslmd.mm"
include "wcel.mm"
include "ccmn.mm"
include "ccnfld.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cress.mm"
include "csrg.mm"
include "cv.mm"
include "cxmu.mm"
include "cicc.mm"
include "cxad.mm"
include "wceq.mm"
include "caddc.mm"
include "w3a.mm"
include "cmul.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "cxrs.mm"
include "xrge0cmn.mm"
include "eqeltri.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "resvcmn.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "rge0srg.mm"
include "icossicc.mm"
include "simplr.mm"
include "sseldi.mm"
include "simprr.mm"
include "ge0xmulcl.mm"
include "syl2anc.mm"
include "simprl.mm"
include "xrge0adddi.mm"
include "syl3anc.mm"
include "cr.mm"
include "rge0ssre.mm"
include "simpll.mm"
include "rexadd.mm"
include "oveq1d.mm"
include "xrge0adddir.mm"
include "eqtr3d.mm"
include "3jca.mm"
include "rexmul.mm"
include "cxr.mm"
include "rexrd.mm"
include "iccssxr.mm"
include "xmulass.mm"
include "xmulid2.mm"
include "syl.mm"
include "xmul02.mm"
include "jca.mm"
include "ralrimivva.mm"
include "rgen2a.mm"
include "cbs.mm"
include "cfv.mm"
include "xrge0base.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "resvbas.mm"
include "cplusg.mm"
include "xrge0plusg.mm"
include "resvplusg.mm"
include "cvsca.mm"
include "ax-xrsvsca.mm"
include "ressvsca.mm"
include "resvvsca.mm"
include "c0g.mm"
include "xrge00.mm"
include "resv0g.mm"
include "crefld.mm"
include "cin.mm"
include "csca.mm"
include "df-refld.mm"
include "oveq1i.mm"
include "reex.mm"
include "ressress.mm"
include "mp2an.mm"
include "eqtri.mm"
include "ax-xrssca.mm"
include "resssca.mm"
include "rebase.mm"
include "resvsca.mm"
include "incom.mm"
include "wss.mm"
include "df-ss.mm"
include "eqtr3i.mm"
include "oveq2i.mm"
include "3eqtr3ri.mm"
include "cc.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "eqid.mm"
include "cnfldbas.mm"
include "ressbas2.mm"
include "cnfldadd.mm"
include "ressplusg.mm"
include "cmulr.mm"
include "cnfldmul.mm"
include "ressmulr.mm"
include "crg.mm"
include "cur.mm"
include "cdr.mm"
include "cndrng.mm"
include "drngring.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "1re.mm"
include "0le1.mm"
include "ltpnf.mm"
include "3pm3.2i.mm"
include "0re.mm"
include "pnfxr.mm"
include "elico2.mm"
include "mpbir.mm"
include "cnfld1.mm"
include "ress1r.mm"
include "mp3an.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "mp2b.mm"
include "0e0icopnf.mm"
include "cnfld0.mm"
include "ress0g.mm"
include "isslmd.mm"
include "mpbir3an.mm"

theorem xrge0slmod
  let cG: class G
  let cW: class W
  let vq: setvar q
  let vr: setvar r
  let vw: setvar w
  let vx: setvar x
  assume xrge0slmod.1: |- G = ( RR*s |`s ( 0 [,] +oo ) )
  assume xrge0slmod.2: |- W = ( G |`v ( 0 [,) +oo ) )


  assert |- W e. SLMod

  proof
    cW
    cslmd
    wcel
    cW
    ccmn
    wcel
    #
    ccnfld
    cc0
    cpnf
    cico
    co
    #
    cress
    co
    #
    csrg
    wcel
    vr
    cv
    #
    vw
    cv
    #
    cxmu
    co
    #
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @3
    @4
    vx
    cv
    #
    cxad
    co
    cxmu
    co
    @5
    @3
    @8
    cxmu
    co
    cxad
    co
    wceq
    #
    vq
    cv
    #
    @3
    caddc
    co
    #
    @4
    cxmu
    co
    #
    @10
    @4
    cxmu
    co
    @5
    cxad
    co
    #
    wceq
    #
    w3a
    #
    @10
    @3
    cmul
    co
    #
    @4
    cxmu
    co
    #
    @10
    @5
    cxmu
    co
    #
    wceq
    #
    c1
    @4
    cxmu
    co
    @4
    wceq
    #
    cc0
    @4
    cxmu
    co
    cc0
    wceq
    #
    w3a
    #
    wa
    #
    vw
    @6
    wral
    vx
    @6
    wral
    #
    vr
    @1
    wral
    vq
    @1
    wral
    cG
    ccmn
    wcel
    #
    @0
    cG
    cxrs
    @6
    cress
    co
    #
    ccmn
    xrge0slmod.1
    xrge0cmn
    eqeltri
    @1
    cvv
    wcel
    #
    @25
    @0
    wb
    cc0
    cpnf
    cico
    ovex
    #
    @1
    cG
    cW
    cvv
    xrge0slmod.2
    resvcmn
    ax-mp
    mpbi
    rge0srg
    @24
    vq
    vr
    @1
    @10
    @1
    wcel
    #
    @3
    @1
    wcel
    #
    wa
    #
    @23
    vx
    vw
    @6
    @6
    @31
    @8
    @6
    wcel
    #
    @4
    @6
    wcel
    #
    wa
    #
    wa
    #
    @15
    @22
    @35
    @7
    @9
    @14
    @35
    @3
    @6
    wcel
    #
    @33
    @7
    @35
    @1
    @6
    @3
    cc0
    cpnf
    icossicc
    #
    @29
    @30
    @34
    simplr
    #
    sseldi
    #
    @31
    @32
    @33
    simprr
    #
    @3
    @4
    ge0xmulcl
    syl2anc
    @35
    @33
    @32
    @36
    @9
    @40
    @31
    @32
    @33
    simprl
    @39
    @4
    @8
    @3
    xrge0adddi
    syl3anc
    @35
    @10
    @3
    cxad
    co
    #
    @4
    cxmu
    co
    #
    @12
    @13
    @35
    @41
    @11
    @4
    cxmu
    @35
    @10
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @41
    @11
    wceq
    @35
    @1
    cr
    @10
    rge0ssre
    @29
    @30
    @34
    simpll
    #
    sseldi
    #
    @35
    @1
    cr
    @3
    rge0ssre
    @38
    sseldi
    #
    @10
    @3
    rexadd
    syl2anc
    oveq1d
    @35
    @10
    @6
    wcel
    @36
    @33
    @42
    @13
    wceq
    @35
    @1
    @6
    @10
    @37
    @45
    sseldi
    @39
    @40
    @10
    @3
    @4
    xrge0adddir
    syl3anc
    eqtr3d
    3jca
    @35
    @19
    @20
    @21
    @35
    @10
    @3
    cxmu
    co
    #
    @4
    cxmu
    co
    #
    @17
    @18
    @35
    @48
    @16
    @4
    cxmu
    @35
    @43
    @44
    @48
    @16
    wceq
    @46
    @47
    @10
    @3
    rexmul
    syl2anc
    oveq1d
    @35
    @10
    cxr
    wcel
    @3
    cxr
    wcel
    @4
    cxr
    wcel
    #
    @49
    @18
    wceq
    @35
    @10
    @46
    rexrd
    @35
    @3
    @47
    rexrd
    @35
    @6
    cxr
    @4
    cc0
    cpnf
    iccssxr
    @40
    sseldi
    #
    @10
    @3
    @4
    xmulass
    syl3anc
    eqtr3d
    @35
    @50
    @20
    @51
    @4
    xmulid2
    syl
    @35
    @50
    @21
    @51
    @4
    xmul02
    syl
    3jca
    jca
    ralrimivva
    rgen2a
    vx
    vw
    cxad
    caddc
    cxmu
    cmul
    c1
    @2
    @1
    cc0
    @6
    cW
    cc0
    vr
    vq
    @27
    @6
    cW
    cbs
    cfv
    wceq
    @28
    @1
    @6
    cG
    cW
    cvv
    xrge0slmod.2
    @6
    @26
    cbs
    cfv
    cG
    cbs
    cfv
    xrge0base
    cG
    @26
    cbs
    xrge0slmod.1
    fveq2i
    eqtr4i
    resvbas
    ax-mp
    @27
    cxad
    cW
    cplusg
    cfv
    wceq
    @28
    @1
    cxad
    cG
    cW
    cvv
    xrge0slmod.2
    cxad
    @26
    cplusg
    cfv
    cG
    cplusg
    cfv
    xrge0plusg
    cG
    @26
    cplusg
    xrge0slmod.1
    fveq2i
    eqtr4i
    resvplusg
    ax-mp
    @27
    cxmu
    cW
    cvsca
    cfv
    wceq
    @28
    @1
    cxmu
    cG
    cW
    cvv
    xrge0slmod.2
    @6
    cvv
    wcel
    #
    cxmu
    cG
    cvsca
    cfv
    wceq
    cc0
    cpnf
    cicc
    ovex
    #
    @6
    cxmu
    cxrs
    cG
    cvv
    xrge0slmod.1
    ax-xrsvsca
    ressvsca
    ax-mp
    resvvsca
    ax-mp
    @27
    cc0
    cW
    c0g
    cfv
    wceq
    @28
    @1
    cG
    cW
    cvv
    cc0
    xrge0slmod.2
    cc0
    @26
    c0g
    cfv
    cG
    c0g
    cfv
    xrge00
    cG
    @26
    c0g
    xrge0slmod.1
    fveq2i
    eqtr4i
    resv0g
    ax-mp
    crefld
    @1
    cress
    co
    #
    ccnfld
    cr
    @1
    cin
    #
    cress
    co
    #
    cW
    csca
    cfv
    #
    @2
    @54
    ccnfld
    cr
    cress
    co
    #
    @1
    cress
    co
    #
    @56
    crefld
    @58
    @1
    cress
    df-refld
    oveq1i
    cr
    cvv
    wcel
    @27
    @59
    @56
    wceq
    reex
    @28
    cr
    @1
    ccnfld
    cvv
    cvv
    ressress
    mp2an
    eqtri
    @27
    @54
    @57
    wceq
    @28
    @1
    cr
    cW
    crefld
    cvv
    cG
    xrge0slmod.2
    @52
    crefld
    cG
    csca
    cfv
    wceq
    @53
    @6
    crefld
    cxrs
    cG
    cvv
    xrge0slmod.1
    ax-xrssca
    resssca
    ax-mp
    rebase
    resvsca
    ax-mp
    @55
    @1
    ccnfld
    cress
    @1
    cr
    cin
    #
    @55
    @1
    @1
    cr
    incom
    @1
    cr
    wss
    @60
    @1
    wceq
    rge0ssre
    @1
    cr
    df-ss
    mpbi
    eqtr3i
    oveq2i
    3eqtr3ri
    @1
    cc
    wss
    #
    @1
    @2
    cbs
    cfv
    wceq
    @1
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    #
    @1
    cc
    @2
    ccnfld
    @2
    eqid
    #
    cnfldbas
    ressbas2
    ax-mp
    @27
    caddc
    @2
    cplusg
    cfv
    wceq
    @28
    @1
    caddc
    ccnfld
    @2
    cvv
    @63
    cnfldadd
    ressplusg
    ax-mp
    @27
    cmul
    @2
    cmulr
    cfv
    wceq
    @28
    @1
    ccnfld
    @2
    cmul
    cvv
    @63
    cnfldmul
    ressmulr
    ax-mp
    ccnfld
    crg
    wcel
    #
    c1
    @1
    wcel
    #
    @61
    c1
    @2
    cur
    cfv
    wceq
    ccnfld
    cdr
    wcel
    #
    @64
    cndrng
    ccnfld
    drngring
    #
    ax-mp
    @65
    c1
    cr
    wcel
    #
    cc0
    c1
    cle
    wbr
    #
    c1
    cpnf
    clt
    wbr
    #
    w3a
    #
    @68
    @69
    @70
    1re
    0le1
    @68
    @70
    1re
    c1
    ltpnf
    ax-mp
    3pm3.2i
    cc0
    cr
    wcel
    cpnf
    cxr
    wcel
    @65
    @71
    wb
    0re
    pnfxr
    cc0
    cpnf
    c1
    elico2
    mp2an
    mpbir
    @62
    @1
    cc
    ccnfld
    @2
    c1
    @63
    cnfldbas
    cnfld1
    ress1r
    mp3an
    ccnfld
    cmnd
    wcel
    #
    cc0
    @1
    wcel
    @61
    cc0
    @2
    c0g
    cfv
    wceq
    @66
    @64
    @72
    cndrng
    @67
    ccnfld
    ringmnd
    mp2b
    0e0icopnf
    @62
    @1
    cc
    ccnfld
    @2
    cc0
    @63
    cnfldbas
    cnfld0
    ress0g
    mp3an
    isslmd
    mpbir3an
end
