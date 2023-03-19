include "cbl.mm"
include "cfv.mm"
include "crn.mm"
include "ctg.mm"
include "cioo.mm"
include "cr.mm"
include "cxmt.mm"
include "wcel.mm"
include "wceq.mm"
include "rexmet.mm"
include "mopnval.mm"
include "ax-mp.mm"
include "wss.mm"
include "blssioo.mm"
include "cv.mm"
include "co.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "cuni.mm"
include "elssuni.mm"
include "unirnioo.mm"
include "syl6sseqr.mm"
include "wa.mm"
include "c1.mm"
include "cin.mm"
include "ctb.mm"
include "retopbas.mm"
include "a1i.mm"
include "simpl.mm"
include "sselda.mm"
include "cmin.mm"
include "caddc.mm"
include "1re.mm"
include "bl2ioo.mm"
include "mpan2.mm"
include "cxr.mm"
include "peano2rem.mm"
include "rexrd.mm"
include "peano2re.mm"
include "cxp.mm"
include "wfn.mm"
include "cpw.mm"
include "wf.mm"
include "ioof.mm"
include "ffn.mm"
include "fnovrn.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "syl.mm"
include "simpr.mm"
include "1rp.mm"
include "blcntr.mm"
include "mp3an13.mm"
include "elind.mm"
include "basis2.mm"
include "syl22anc.mm"
include "wb.mm"
include "ovelrn.mm"
include "wi.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "inss2.mm"
include "sstr.mm"
include "adantl.mm"
include "elioore.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "dfss.mm"
include "sylib.mm"
include "eliooxr.mm"
include "jca.mm"
include "iooin.mm"
include "eqtrd.mm"
include "cmnf.mm"
include "clt.mm"
include "mnfxr.mm"
include "simpld.mm"
include "ifcld.mm"
include "simprd.mm"
include "mnflt.mm"
include "xrmax2.mm"
include "xrltletrd.mm"
include "eleqtrd.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "ioon0.mm"
include "syl5ib.mm"
include "mpcom.mm"
include "xrre2.mm"
include "syl32anc.mm"
include "mnfle.mm"
include "xrlelttrd.mm"
include "xrmin2.mm"
include "xrre.mm"
include "ioo2blex.mm"
include "inss1.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "blssex.mm"
include "sylancr.mm"
include "mpbid.mm"
include "syl6bi.mm"
include "rexlimivv.mm"
include "imp.mm"
include "sylanb.mm"
include "rexlimiva.mm"
include "ralrimiva.mm"
include "elmopn2.mm"
include "sylanbrc.mm"
include "ssriv.mm"
include "sseqtri.mm"
include "2basgen.mm"
include "mp2an.mm"
include "eqtr2i.mm"

theorem tgioo
  let cD: class D
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vr: setvar r
  let cA: class A
  let cB: class B
  assume remet.1: |- D = ( ( abs o. - ) |` ( RR X. RR ) )
  assume tgioo.2: |- J = ( MetOpen ` D )


  assert |- ( topGen ` ran (,) ) = J

  proof
    cJ
    cD
    cbl
    cfv
    #
    crn
    #
    ctg
    cfv
    #
    cioo
    crn
    #
    ctg
    cfv
    #
    cD
    cr
    cxmt
    cfv
    wcel
    #
    cJ
    @2
    wceq
    cD
    remet.1
    rexmet
    #
    cD
    cJ
    cr
    tgioo.2
    mopnval
    ax-mp
    #
    @1
    @3
    wss
    @3
    @2
    wss
    @2
    @4
    wceq
    cD
    remet.1
    blssioo
    @3
    cJ
    @2
    vv
    @3
    cJ
    vv
    cv
    #
    @3
    wcel
    #
    @8
    cr
    wss
    #
    vx
    cv
    #
    vy
    cv
    @0
    co
    @8
    wss
    vy
    crp
    wrex
    #
    vx
    @8
    wral
    #
    @8
    cJ
    wcel
    #
    @9
    @8
    @3
    cuni
    cr
    @8
    @3
    elssuni
    unirnioo
    syl6sseqr
    #
    @9
    @12
    vx
    @8
    @9
    @11
    @8
    wcel
    #
    wa
    #
    @11
    vz
    cv
    #
    wcel
    #
    @18
    @8
    @11
    c1
    @0
    co
    #
    cin
    #
    wss
    #
    wa
    #
    vz
    @3
    wrex
    #
    @12
    @17
    @3
    ctb
    wcel
    #
    @9
    @20
    @3
    wcel
    #
    @11
    @21
    wcel
    @24
    @25
    @17
    retopbas
    a1i
    @9
    @16
    simpl
    @17
    @11
    cr
    wcel
    #
    @26
    @9
    @8
    cr
    @11
    @15
    sselda
    #
    @27
    @20
    @11
    c1
    cmin
    co
    #
    @11
    c1
    caddc
    co
    #
    cioo
    co
    #
    @3
    @27
    c1
    cr
    wcel
    @20
    @31
    wceq
    #
    1re
    @11
    c1
    cD
    remet.1
    bl2ioo
    mpan2
    #
    @27
    @29
    cxr
    wcel
    #
    @30
    cxr
    wcel
    #
    @31
    @3
    wcel
    #
    @27
    @29
    @11
    peano2rem
    #
    rexrd
    #
    @27
    @30
    @11
    peano2re
    #
    rexrd
    #
    cioo
    cxr
    cxr
    cxp
    #
    wfn
    #
    @34
    @35
    @36
    @41
    cr
    cpw
    #
    cioo
    wf
    @42
    ioof
    @41
    @43
    cioo
    ffn
    ax-mp
    #
    cxr
    cxr
    @29
    @30
    cioo
    fnovrn
    mp3an1
    syl2anc
    eqeltrd
    syl
    @17
    @8
    @20
    @11
    @9
    @16
    simpr
    @17
    @27
    @11
    @20
    wcel
    #
    @28
    @5
    @27
    c1
    crp
    wcel
    @45
    @6
    1rp
    cD
    @11
    c1
    cr
    blcntr
    mp3an13
    syl
    elind
    vz
    @11
    @3
    @8
    @20
    basis2
    syl22anc
    @23
    @12
    vz
    @3
    @18
    @3
    wcel
    #
    @18
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
    va
    cxr
    wrex
    #
    @23
    @12
    @42
    @46
    @51
    wb
    @44
    va
    vb
    cxr
    cxr
    @18
    cioo
    ovelrn
    ax-mp
    @51
    @23
    @12
    @50
    @23
    @12
    wi
    #
    va
    vb
    cxr
    cxr
    @50
    @52
    wi
    @47
    cxr
    wcel
    #
    @48
    cxr
    wcel
    #
    wa
    #
    @50
    @23
    @11
    @49
    wcel
    #
    @49
    @21
    wss
    #
    wa
    #
    @12
    @50
    @19
    @56
    @22
    @57
    @18
    @49
    @11
    eleq2
    #
    @18
    @49
    @21
    sseq1
    anbi12d
    @58
    @19
    @18
    @8
    wss
    #
    wa
    #
    vz
    @1
    wrex
    #
    @12
    @58
    @49
    @1
    wcel
    @56
    @49
    @8
    wss
    #
    @62
    @58
    @49
    @47
    @29
    cle
    wbr
    #
    @29
    @47
    cif
    #
    @48
    @30
    cle
    wbr
    #
    @48
    @30
    cif
    #
    cioo
    co
    #
    @1
    @58
    @49
    @49
    @31
    cin
    #
    @68
    @58
    @49
    @31
    wss
    @49
    @69
    wceq
    @58
    @49
    @20
    @31
    @57
    @49
    @20
    wss
    #
    @56
    @57
    @21
    @20
    wss
    @70
    @8
    @20
    inss2
    @49
    @21
    @20
    sstr
    mpan2
    adantl
    @58
    @27
    @32
    @56
    @27
    @57
    @11
    @47
    @48
    elioore
    #
    adantr
    #
    @33
    syl
    sseqtrd
    @49
    @31
    dfss
    sylib
    @56
    @69
    @68
    wceq
    #
    @57
    @56
    @55
    @34
    @35
    wa
    #
    @73
    @11
    @47
    @48
    eliooxr
    #
    @56
    @27
    @74
    @71
    @27
    @34
    @35
    @38
    @40
    jca
    syl
    @47
    @48
    @29
    @30
    iooin
    syl2anc
    adantr
    eqtrd
    #
    @58
    @65
    cr
    wcel
    #
    @67
    cr
    wcel
    #
    @68
    @1
    wcel
    @58
    cmnf
    cxr
    wcel
    #
    @65
    cxr
    wcel
    #
    @67
    cxr
    wcel
    #
    cmnf
    @65
    clt
    wbr
    @65
    @67
    clt
    wbr
    #
    @77
    @79
    @58
    mnfxr
    a1i
    #
    @58
    @64
    @29
    @47
    cxr
    @58
    @27
    @34
    @72
    @38
    syl
    #
    @58
    @53
    @54
    @56
    @55
    @57
    @75
    adantr
    #
    simpld
    #
    ifcld
    #
    @58
    @66
    @48
    @30
    cxr
    @58
    @53
    @54
    @85
    simprd
    #
    @58
    @30
    @58
    @27
    @30
    cr
    wcel
    #
    @72
    @39
    syl
    #
    rexrd
    #
    ifcld
    #
    @58
    cmnf
    @29
    @65
    @83
    @84
    @87
    @58
    @29
    cr
    wcel
    #
    cmnf
    @29
    clt
    wbr
    @56
    @93
    @57
    @56
    @27
    @93
    @71
    @37
    syl
    adantr
    @29
    mnflt
    syl
    @58
    @53
    @34
    @29
    @65
    cle
    wbr
    @86
    @84
    @47
    @29
    xrmax2
    syl2anc
    xrltletrd
    @58
    @11
    @68
    wcel
    #
    @82
    @58
    @11
    @49
    @68
    @56
    @57
    simpl
    #
    @76
    eleqtrd
    @80
    @81
    wa
    #
    @94
    @82
    @11
    @65
    @67
    eliooxr
    @94
    @68
    c0
    wne
    @96
    @82
    @68
    @11
    ne0i
    @65
    @67
    ioon0
    syl5ib
    mpcom
    syl
    #
    cmnf
    @65
    @67
    xrre2
    syl32anc
    @58
    @81
    @89
    cmnf
    @67
    clt
    wbr
    @67
    @30
    cle
    wbr
    #
    @78
    @92
    @90
    @58
    cmnf
    @65
    @67
    @83
    @87
    @92
    @58
    @80
    cmnf
    @65
    cle
    wbr
    @87
    @65
    mnfle
    syl
    @97
    xrlelttrd
    @58
    @54
    @35
    @98
    @88
    @91
    @48
    @30
    xrmin2
    syl2anc
    @67
    @30
    xrre
    syl22anc
    @65
    @67
    cD
    remet.1
    ioo2blex
    syl2anc
    eqeltrd
    @95
    @57
    @63
    @56
    @57
    @21
    @8
    wss
    @63
    @8
    @20
    inss1
    @49
    @21
    @8
    sstr
    mpan2
    adantl
    @61
    @56
    @63
    wa
    vz
    @49
    @1
    @50
    @19
    @56
    @60
    @63
    @59
    @18
    @49
    @8
    sseq1
    anbi12d
    rspcev
    syl12anc
    @58
    @5
    @27
    @62
    @12
    wb
    @6
    @72
    vz
    @8
    cD
    @11
    cr
    vy
    blssex
    sylancr
    mpbid
    syl6bi
    a1i
    rexlimivv
    imp
    sylanb
    rexlimiva
    syl
    ralrimiva
    @5
    @14
    @10
    @13
    wa
    wb
    @6
    vx
    vy
    @8
    cD
    cJ
    cr
    tgioo.2
    elmopn2
    ax-mp
    sylanbrc
    ssriv
    @7
    sseqtri
    @1
    @3
    2basgen
    mp2an
    eqtr2i
end
