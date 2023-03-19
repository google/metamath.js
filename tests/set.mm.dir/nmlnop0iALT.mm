include "cnop.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "ch0o.mm"
include "cv.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "c0v.mm"
include "wne.mm"
include "wn.mm"
include "c1.mm"
include "cno.mm"
include "cdiv.mm"
include "co.mm"
include "csm.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "cc.mm"
include "normcl.mm"
include "recnd.mm"
include "adantr.mm"
include "norm-i.mm"
include "fveq2.mm"
include "lnop0i.mm"
include "syl6eq.mm"
include "syl6bi.mm"
include "necon3d.mm"
include "imp.mm"
include "recne0d.mm"
include "simpr.mm"
include "wo.mm"
include "wb.mm"
include "reccld.mm"
include "lnopfi.mm"
include "ffvelrni.mm"
include "hvmul0or.mm"
include "syl2anc.mm"
include "necon3abid.mm"
include "neanior.mm"
include "syl6bbr.mm"
include "mpbir2and.mm"
include "hvmulcl.mm"
include "normgt0.mm"
include "syl.mm"
include "mpbid.mm"
include "ex.mm"
include "adantl.mm"
include "cle.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "csup.mm"
include "wss.mm"
include "cr.mm"
include "wf.mm"
include "nmopsetretHIL.mm"
include "ax-mp.mm"
include "ressxr.mm"
include "sstri.mm"
include "simpl.mm"
include "necon3i.mm"
include "norm1.mm"
include "sylan2.mm"
include "1re.mm"
include "syl6eqel.mm"
include "eqle.mm"
include "lnopmuli.mm"
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
include "sylancr.mm"
include "adantll.mm"
include "nmopval.mm"
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
include "ho0val.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "ffn.mm"
include "ho0f.mm"
include "eqfnfv.mm"
include "mp2an.mm"
include "nmop0.mm"
include "impbii.mm"

theorem nmlnop0iALT
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nmlnop0.1: |- T e. LinOp


  assert |- ( ( normop ` T ) = 0 <-> T = 0hop )

  proof
    cT
    cnop
    cfv
    #
    cc0
    wceq
    #
    cT
    ch0o
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
    ch0o
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    #
    @2
    @1
    @6
    vx
    chil
    @1
    @3
    chil
    wcel
    #
    wa
    #
    @4
    c0v
    @5
    @9
    @4
    c0v
    wne
    #
    wn
    @4
    c0v
    wceq
    #
    @9
    @10
    cc0
    c1
    @3
    cno
    cfv
    #
    cdiv
    co
    #
    @4
    csm
    co
    #
    cno
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
    c0v
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
    @3
    normcl
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
    c0v
    @8
    @12
    cc0
    wceq
    @3
    c0v
    wceq
    #
    @11
    @3
    norm-i
    @21
    @4
    c0v
    cT
    cfv
    c0v
    @3
    c0v
    cT
    fveq2
    cT
    nmlnop0.1
    lnop0i
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
    @24
    @14
    c0v
    @17
    @13
    cc
    wcel
    #
    @4
    chil
    wcel
    #
    @14
    c0v
    wceq
    @24
    wb
    @17
    @12
    @20
    @23
    reccld
    #
    @8
    @26
    @10
    chil
    chil
    @3
    cT
    cT
    nmlnop0.1
    lnopfi
    #
    ffvelrni
    adantr
    #
    @13
    @4
    hvmul0or
    syl2anc
    necon3abid
    @13
    cc0
    @4
    c0v
    neanior
    syl6bbr
    mpbir2and
    @17
    @14
    chil
    wcel
    #
    @18
    @16
    wb
    @17
    @25
    @26
    @30
    @27
    @29
    @13
    @4
    hvmulcl
    syl2anc
    #
    @14
    normgt0
    syl
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
    @32
    @33
    @15
    vz
    cv
    #
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    vy
    cv
    #
    @35
    cT
    cfv
    #
    cno
    cfv
    #
    wceq
    #
    wa
    #
    vz
    chil
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
    @45
    cle
    wbr
    #
    @1
    @17
    @44
    cxr
    wss
    @15
    @44
    wcel
    #
    @46
    @44
    cr
    cxr
    chil
    chil
    cT
    wf
    #
    @44
    cr
    wss
    @28
    vy
    vz
    cT
    nmopsetretHIL
    ax-mp
    ressxr
    sstri
    @17
    @37
    @15
    @40
    wceq
    #
    wa
    #
    vz
    chil
    wrex
    #
    @47
    @17
    @13
    @3
    csm
    co
    #
    chil
    wcel
    #
    @52
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    @15
    @52
    cT
    cfv
    #
    cno
    cfv
    #
    wceq
    #
    @51
    @17
    @25
    @8
    @53
    @27
    @8
    @10
    simpl
    #
    @13
    @3
    hvmulcl
    syl2anc
    @17
    @54
    cr
    wcel
    @54
    c1
    wceq
    #
    @55
    @17
    @54
    c1
    cr
    @10
    @8
    @3
    c0v
    wne
    @60
    @3
    c0v
    @4
    c0v
    @22
    necon3i
    @3
    norm1
    sylan2
    #
    1re
    syl6eqel
    @61
    @54
    c1
    eqle
    syl2anc
    @17
    @14
    @56
    cno
    @17
    @56
    @14
    @17
    @25
    @8
    @56
    @14
    wceq
    @27
    @59
    @13
    @3
    cT
    nmlnop0.1
    lnopmuli
    syl2anc
    eqcomd
    fveq2d
    @50
    @55
    @58
    wa
    vz
    @52
    chil
    @35
    @52
    wceq
    #
    @37
    @55
    @49
    @58
    @62
    @36
    @54
    c1
    cle
    @35
    @52
    cno
    fveq2
    breq1d
    @62
    @40
    @57
    @15
    @62
    @39
    @56
    cno
    @35
    @52
    cT
    fveq2
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    @43
    @51
    vy
    @15
    @14
    cno
    fvex
    @38
    @15
    wceq
    #
    @42
    @50
    vz
    chil
    @63
    @41
    @49
    @37
    @38
    @15
    @40
    eqeq1
    anbi2d
    rexbidv
    elab
    sylibr
    @44
    @15
    supxrub
    sylancr
    adantll
    @1
    @45
    cc0
    wceq
    #
    @8
    @10
    @1
    @64
    @0
    @45
    cc0
    @48
    @0
    @45
    wceq
    @28
    vy
    vz
    cT
    nmopval
    ax-mp
    eqeq1i
    biimpi
    ad2antrr
    breqtrd
    @8
    @10
    @34
    @32
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
    @65
    @17
    @30
    @66
    @31
    @14
    normcl
    syl
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
    c0v
    nne
    sylib
    @8
    @5
    c0v
    wceq
    @1
    @3
    ho0val
    adantl
    eqtr4d
    ralrimiva
    cT
    chil
    wfn
    #
    ch0o
    chil
    wfn
    #
    @2
    @7
    wb
    @48
    @67
    @28
    chil
    chil
    cT
    ffn
    ax-mp
    chil
    chil
    ch0o
    wf
    @68
    ho0f
    chil
    chil
    ch0o
    ffn
    ax-mp
    vx
    chil
    cT
    ch0o
    eqfnfv
    mp2an
    sylibr
    @2
    @0
    ch0o
    cnop
    cfv
    cc0
    cT
    ch0o
    cnop
    fveq2
    nmop0
    syl6eq
    impbii
end
