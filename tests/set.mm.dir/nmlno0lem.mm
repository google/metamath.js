include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "wn.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "cc.mm"
include "cnv.mm"
include "cr.mm"
include "nvcl.mm"
include "mpan.mm"
include "recnd.mm"
include "adantr.mm"
include "wb.mm"
include "nvz.mm"
include "fveq2.mm"
include "lno0.mm"
include "mp3an.mm"
include "syl6eq.mm"
include "syl6bi.mm"
include "necon3d.mm"
include "imp.mm"
include "recne0d.mm"
include "simpr.mm"
include "wo.mm"
include "reccld.mm"
include "wf.mm"
include "lnof.mm"
include "ffvelrni.mm"
include "nvmul0or.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "necon3abid.mm"
include "neanior.mm"
include "syl6bbr.mm"
include "mpbir2and.mm"
include "nvscl.mm"
include "nvgt0.mm"
include "sylancr.mm"
include "mpbid.mm"
include "ex.mm"
include "adantl.mm"
include "cle.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "csup.mm"
include "wss.mm"
include "nmosetre.mm"
include "mp2an.mm"
include "ressxr.mm"
include "sstri.mm"
include "simpl.mm"
include "necon3i.mm"
include "nv1.mm"
include "sylan2.mm"
include "1re.mm"
include "syl6eqel.mm"
include "eqle.mm"
include "w3a.mm"
include "3pm3.2i.mm"
include "lnomul.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "fvex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elab.mm"
include "sylibr.mm"
include "supxrub.mm"
include "adantll.mm"
include "nmooval.mm"
include "eqeq1i.mm"
include "biimpi.mm"
include "ad2antrr.mm"
include "breqtrd.mm"
include "0re.mm"
include "lenlt.mm"
include "sylancl.mm"
include "pm2.65d.mm"
include "nne.mm"
include "sylib.mm"
include "0oval.mm"
include "mp3an12.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "ffn.mm"
include "ax-mp.mm"
include "0oo.mm"
include "eqfnfv.mm"
include "nmoo0.mm"
include "impbii.mm"

theorem nmlno0lem
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume nmlno0.3: |- N = ( U normOpOLD W )
  assume nmlno0.0: |- Z = ( U 0op W )
  assume nmlno0.7: |- L = ( U LnOp W )
  assume nmlno0lem.u: |- U e. NrmCVec
  assume nmlno0lem.w: |- W e. NrmCVec
  assume nmlno0lem.l: |- T e. L
  assume nmlno0lem.1: |- X = ( BaseSet ` U )
  assume nmlno0lem.2: |- Y = ( BaseSet ` W )
  assume nmlno0lem.r: |- R = ( .sOLD ` U )
  assume nmlno0lem.s: |- S = ( .sOLD ` W )
  assume nmlno0lem.p: |- P = ( 0vec ` U )
  assume nmlno0lem.q: |- Q = ( 0vec ` W )
  assume nmlno0lem.k: |- K = ( normCV ` U )
  assume nmlno0lem.m: |- M = ( normCV ` W )


  assert |- ( ( N ` T ) = 0 <-> T = Z )

  proof
    cT
    cN
    cfv
    #
    cc0
    wceq
    #
    cT
    cZ
    wceq
    #
    @1
    vx
    cv
    #
    cT
    cfv
    #
    @3
    cZ
    cfv
    #
    wceq
    #
    vx
    cX
    wral
    #
    @2
    @1
    @6
    vx
    cX
    @1
    @3
    cX
    wcel
    #
    wa
    #
    @4
    cQ
    @5
    @9
    @4
    cQ
    wne
    #
    wn
    @4
    cQ
    wceq
    #
    @9
    @10
    cc0
    c1
    @3
    cK
    cfv
    #
    cdiv
    co
    #
    @4
    cS
    co
    #
    cM
    cfv
    #
    clt
    wbr
    #
    @8
    @10
    @16
    wi
    @1
    @8
    @10
    @16
    @8
    @10
    wa
    #
    @14
    cQ
    wne
    #
    @16
    @17
    @18
    @13
    cc0
    wne
    #
    @10
    @17
    @12
    @8
    @12
    cc
    wcel
    @10
    @8
    @12
    cU
    cnv
    wcel
    #
    @8
    @12
    cr
    wcel
    nmlno0lem.u
    @3
    cU
    cK
    cX
    nmlno0lem.1
    nmlno0lem.k
    nvcl
    mpan
    recnd
    adantr
    #
    @8
    @10
    @12
    cc0
    wne
    @8
    @12
    cc0
    @4
    cQ
    @8
    @12
    cc0
    wceq
    #
    @3
    cP
    wceq
    #
    @11
    @20
    @8
    @22
    @23
    wb
    nmlno0lem.u
    @3
    cU
    cK
    cX
    cP
    nmlno0lem.1
    nmlno0lem.p
    nmlno0lem.k
    nvz
    mpan
    @23
    @4
    cP
    cT
    cfv
    #
    cQ
    @3
    cP
    cT
    fveq2
    @20
    cW
    cnv
    wcel
    #
    cT
    cL
    wcel
    #
    @24
    cQ
    wceq
    nmlno0lem.u
    nmlno0lem.w
    nmlno0lem.l
    cP
    cT
    cU
    cL
    cW
    cX
    cY
    cQ
    nmlno0lem.1
    nmlno0lem.2
    nmlno0lem.p
    nmlno0lem.q
    nmlno0.7
    lno0
    mp3an
    syl6eq
    #
    syl6bi
    necon3d
    imp
    #
    recne0d
    @8
    @10
    simpr
    @17
    @18
    @13
    cc0
    wceq
    @11
    wo
    #
    wn
    @19
    @10
    wa
    @17
    @29
    @14
    cQ
    @17
    @13
    cc
    wcel
    #
    @4
    cY
    wcel
    #
    @14
    cQ
    wceq
    @29
    wb
    #
    @17
    @12
    @21
    @28
    reccld
    #
    @8
    @31
    @10
    cX
    cY
    @3
    cT
    @20
    @25
    @26
    cX
    cY
    cT
    wf
    #
    nmlno0lem.u
    nmlno0lem.w
    nmlno0lem.l
    cT
    cU
    cL
    cW
    cX
    cY
    nmlno0lem.1
    nmlno0lem.2
    nmlno0.7
    lnof
    mp3an
    #
    ffvelrni
    adantr
    #
    @25
    @30
    @31
    @32
    nmlno0lem.w
    @13
    @4
    cS
    cW
    cY
    cQ
    nmlno0lem.2
    nmlno0lem.s
    nmlno0lem.q
    nvmul0or
    mp3an1
    syl2anc
    necon3abid
    @13
    cc0
    @4
    cQ
    neanior
    syl6bbr
    mpbir2and
    @17
    @25
    @14
    cY
    wcel
    #
    @18
    @16
    wb
    nmlno0lem.w
    @17
    @30
    @31
    @37
    @33
    @36
    @25
    @30
    @31
    @37
    nmlno0lem.w
    @13
    @4
    cS
    cW
    cY
    nmlno0lem.2
    nmlno0lem.s
    nvscl
    mp3an1
    syl2anc
    #
    @14
    cW
    cM
    cY
    cQ
    nmlno0lem.2
    nmlno0lem.q
    nmlno0lem.m
    nvgt0
    sylancr
    mpbid
    ex
    adantl
    @9
    @10
    @16
    wn
    #
    @9
    @10
    wa
    #
    @15
    cc0
    cle
    wbr
    #
    @39
    @40
    @15
    vz
    cv
    #
    cK
    cfv
    #
    c1
    cle
    wbr
    #
    vy
    cv
    #
    @42
    cT
    cfv
    #
    cM
    cfv
    #
    wceq
    #
    wa
    #
    vz
    cX
    wrex
    #
    vy
    cab
    #
    cxr
    clt
    csup
    #
    cc0
    cle
    @8
    @10
    @15
    @52
    cle
    wbr
    #
    @1
    @17
    @51
    cxr
    wss
    @15
    @51
    wcel
    #
    @53
    @51
    cr
    cxr
    @25
    @34
    @51
    cr
    wss
    nmlno0lem.w
    @35
    vy
    vz
    cT
    cK
    cM
    cW
    cX
    cY
    nmlno0lem.2
    nmlno0lem.m
    nmosetre
    mp2an
    ressxr
    sstri
    @17
    @44
    @15
    @47
    wceq
    #
    wa
    #
    vz
    cX
    wrex
    #
    @54
    @17
    @13
    @3
    cR
    co
    #
    cX
    wcel
    #
    @58
    cK
    cfv
    #
    c1
    cle
    wbr
    #
    @15
    @58
    cT
    cfv
    #
    cM
    cfv
    #
    wceq
    #
    @57
    @17
    @30
    @8
    @59
    @33
    @8
    @10
    simpl
    #
    @20
    @30
    @8
    @59
    nmlno0lem.u
    @13
    @3
    cR
    cU
    cX
    nmlno0lem.1
    nmlno0lem.r
    nvscl
    mp3an1
    syl2anc
    @17
    @60
    cr
    wcel
    @60
    c1
    wceq
    #
    @61
    @17
    @60
    c1
    cr
    @10
    @8
    @3
    cP
    wne
    #
    @66
    @3
    cP
    @4
    cQ
    @27
    necon3i
    @20
    @8
    @67
    @66
    nmlno0lem.u
    @3
    cR
    cU
    cK
    cX
    cP
    nmlno0lem.1
    nmlno0lem.r
    nmlno0lem.p
    nmlno0lem.k
    nv1
    mp3an1
    sylan2
    #
    1re
    syl6eqel
    @68
    @60
    c1
    eqle
    syl2anc
    @17
    @14
    @62
    cM
    @17
    @62
    @14
    @17
    @30
    @8
    @62
    @14
    wceq
    #
    @33
    @65
    @20
    @25
    @26
    w3a
    @30
    @8
    wa
    @69
    @20
    @25
    @26
    nmlno0lem.u
    nmlno0lem.w
    nmlno0lem.l
    3pm3.2i
    @13
    @3
    cR
    cS
    cT
    cU
    cL
    cW
    cX
    nmlno0lem.1
    nmlno0lem.r
    nmlno0lem.s
    nmlno0.7
    lnomul
    mpan
    syl2anc
    eqcomd
    fveq2d
    @56
    @61
    @64
    wa
    vz
    @58
    cX
    @42
    @58
    wceq
    #
    @44
    @61
    @55
    @64
    @70
    @43
    @60
    c1
    cle
    @42
    @58
    cK
    fveq2
    breq1d
    @70
    @47
    @63
    @15
    @70
    @46
    @62
    cM
    @42
    @58
    cT
    fveq2
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    @50
    @57
    vy
    @15
    @14
    cM
    fvex
    @45
    @15
    wceq
    #
    @49
    @56
    vz
    cX
    @71
    @48
    @55
    @44
    @45
    @15
    @47
    eqeq1
    anbi2d
    rexbidv
    elab
    sylibr
    @51
    @15
    supxrub
    sylancr
    adantll
    @1
    @52
    cc0
    wceq
    #
    @8
    @10
    @1
    @72
    @0
    @52
    cc0
    @20
    @25
    @34
    @0
    @52
    wceq
    nmlno0lem.u
    nmlno0lem.w
    @35
    vy
    vz
    cT
    cU
    cK
    cM
    cN
    cW
    cX
    cY
    nmlno0lem.1
    nmlno0lem.2
    nmlno0lem.k
    nmlno0lem.m
    nmlno0.3
    nmooval
    mp3an
    eqeq1i
    biimpi
    ad2antrr
    breqtrd
    @8
    @10
    @41
    @39
    wb
    #
    @1
    @17
    @15
    cr
    wcel
    #
    cc0
    cr
    wcel
    @73
    @17
    @25
    @37
    @74
    nmlno0lem.w
    @38
    @14
    cW
    cM
    cY
    nmlno0lem.2
    nmlno0lem.m
    nvcl
    sylancr
    0re
    @15
    cc0
    lenlt
    sylancl
    adantll
    mpbid
    ex
    pm2.65d
    @4
    cQ
    nne
    sylib
    @8
    @5
    cQ
    wceq
    #
    @1
    @20
    @25
    @8
    @75
    nmlno0lem.u
    nmlno0lem.w
    @3
    cU
    cZ
    cW
    cX
    cQ
    nmlno0lem.1
    nmlno0lem.q
    nmlno0.0
    0oval
    mp3an12
    adantl
    eqtr4d
    ralrimiva
    cT
    cX
    wfn
    #
    cZ
    cX
    wfn
    #
    @2
    @7
    wb
    @34
    @76
    @35
    cX
    cY
    cT
    ffn
    ax-mp
    cX
    cY
    cZ
    wf
    #
    @77
    @20
    @25
    @78
    nmlno0lem.u
    nmlno0lem.w
    cU
    cW
    cX
    cY
    cZ
    nmlno0lem.1
    nmlno0lem.2
    nmlno0.0
    0oo
    mp2an
    cX
    cY
    cZ
    ffn
    ax-mp
    vx
    cX
    cT
    cZ
    eqfnfv
    mp2an
    sylibr
    @2
    @0
    cZ
    cN
    cfv
    #
    cc0
    cT
    cZ
    cN
    fveq2
    @20
    @25
    @79
    cc0
    wceq
    nmlno0lem.u
    nmlno0lem.w
    cU
    cN
    cW
    cZ
    nmlno0.3
    nmlno0.0
    nmoo0
    mp2an
    syl6eq
    impbii
end
