include "chil.mm"
include "wcel.mm"
include "cbr.mm"
include "cfv.mm"
include "cnmf.mm"
include "cno.mm"
include "wceq.mm"
include "c0v.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cc.mm"
include "wf.mm"
include "brafn.mm"
include "nmfnval.mm"
include "syl.mm"
include "adantr.mm"
include "wss.mm"
include "wral.mm"
include "wi.mm"
include "cr.mm"
include "nmfnsetre.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "normcl.mm"
include "rexrd.mm"
include "jca.mm"
include "vex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elab.mm"
include "csp.mm"
include "co.mm"
include "id.mm"
include "braval.mm"
include "sylan9eqr.mm"
include "bcs2.mm"
include "3expa.mm"
include "ancom1s.mm"
include "eqbrtrd.mm"
include "exp41.mm"
include "imp4a.mm"
include "rexlimdv.mm"
include "imp.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "cdiv.mm"
include "csm.mm"
include "recnd.mm"
include "cc0.mm"
include "normne0.mm"
include "biimpar.mm"
include "reccld.mm"
include "simpl.mm"
include "hvmulcl.mm"
include "syl2anc.mm"
include "norm1.mm"
include "1le1.mm"
include "syl6eqbr.mm"
include "cmul.mm"
include "ax-his3.mm"
include "syl3anc.mm"
include "rereccld.mm"
include "hiidrcl.mm"
include "remulcld.mm"
include "eqeltrd.mm"
include "normgt0.mm"
include "biimpa.mm"
include "recgt0d.mm"
include "0re.mm"
include "ltle.mm"
include "mpan.mm"
include "sylc.mm"
include "hiidge0.mm"
include "mulge0d.mm"
include "breqtrrd.mm"
include "absidd.mm"
include "recid2d.mm"
include "oveq2d.mm"
include "mul12d.mm"
include "c2.mm"
include "cexp.mm"
include "sqvald.mm"
include "normsq.mm"
include "eqtr3d.mm"
include "eqtrd.mm"
include "mulid1d.mm"
include "3eqtr3rd.mm"
include "3eqtr4rd.mm"
include "breq1d.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "wb.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "fvex.mm"
include "sylibr.mm"
include "breq2.mm"
include "sylan.mm"
include "adantlr.mm"
include "ex.mm"
include "supxr2.mm"
include "csn.mm"
include "cxp.mm"
include "nmfn0.mm"
include "bra0.mm"
include "fveq2i.mm"
include "norm0.mm"
include "3eqtr4i.mm"
include "a1i.mm"
include "pm2.61ne.mm"

theorem branmfn
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cT: class T
  let cU: class U


  assert |- ( A e. ~H -> ( normfn ` ( bra ` A ) ) = ( normh ` A ) )

  proof
    cA
    chil
    wcel
    #
    cA
    cbr
    cfv
    #
    cnmf
    cfv
    #
    cA
    cno
    cfv
    #
    wceq
    c0v
    cbr
    cfv
    #
    cnmf
    cfv
    #
    c0v
    cno
    cfv
    #
    wceq
    #
    cA
    c0v
    cA
    c0v
    wceq
    #
    @2
    @5
    @3
    @6
    @8
    @1
    @4
    cnmf
    cA
    c0v
    cbr
    fveq2
    fveq2d
    cA
    c0v
    cno
    fveq2
    eqeq12d
    @0
    cA
    c0v
    wne
    #
    wa
    #
    @2
    vy
    cv
    #
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    vx
    cv
    #
    @11
    @1
    cfv
    #
    cabs
    cfv
    #
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    #
    @3
    @0
    @2
    @21
    wceq
    #
    @9
    @0
    chil
    cc
    @1
    wf
    #
    @22
    cA
    brafn
    #
    vx
    vy
    @1
    nmfnval
    syl
    adantr
    @10
    @20
    cxr
    wss
    #
    @3
    cxr
    wcel
    #
    wa
    #
    vz
    cv
    #
    @3
    cle
    wbr
    #
    vz
    @20
    wral
    #
    @28
    @3
    clt
    wbr
    #
    @28
    vw
    cv
    #
    clt
    wbr
    #
    vw
    @20
    wrex
    #
    wi
    #
    vz
    cr
    wral
    @21
    @3
    wceq
    @0
    @27
    @9
    @0
    @25
    @26
    @0
    @20
    cr
    cxr
    @0
    @23
    @20
    cr
    wss
    @24
    vx
    vy
    @1
    nmfnsetre
    syl
    ressxr
    syl6ss
    @0
    @3
    cA
    normcl
    #
    rexrd
    jca
    adantr
    @0
    @30
    @9
    @0
    @29
    vz
    @20
    @28
    @20
    wcel
    @0
    @13
    @28
    @16
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    @29
    @19
    @39
    vx
    @28
    vz
    vex
    @14
    @28
    wceq
    #
    @18
    @38
    vy
    chil
    @40
    @17
    @37
    @13
    @14
    @28
    @16
    eqeq1
    anbi2d
    rexbidv
    elab
    @0
    @39
    @29
    @0
    @38
    @29
    vy
    chil
    @0
    @11
    chil
    wcel
    #
    @13
    @37
    @29
    @0
    @41
    @13
    @37
    @29
    @0
    @41
    wa
    #
    @13
    wa
    #
    @37
    wa
    @28
    @11
    cA
    csp
    co
    #
    cabs
    cfv
    #
    @3
    cle
    @37
    @43
    @28
    @16
    @45
    @37
    id
    @42
    @16
    @45
    wceq
    @13
    @42
    @15
    @44
    cabs
    cA
    @11
    braval
    fveq2d
    #
    adantr
    sylan9eqr
    @43
    @45
    @3
    cle
    wbr
    #
    @37
    @41
    @0
    @13
    @47
    @41
    @0
    @13
    @47
    @11
    cA
    bcs2
    3expa
    ancom1s
    adantr
    eqbrtrd
    exp41
    imp4a
    rexlimdv
    imp
    sylan2b
    ralrimiva
    adantr
    @10
    @35
    vz
    cr
    @10
    @28
    cr
    wcel
    #
    wa
    @31
    @34
    @10
    @31
    @34
    @48
    @10
    @3
    @20
    wcel
    #
    @31
    @34
    @10
    @13
    @3
    @16
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    @49
    @10
    @52
    @13
    @3
    @45
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    @10
    c1
    @3
    cdiv
    co
    #
    cA
    csm
    co
    #
    chil
    wcel
    #
    @57
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    @3
    @57
    cA
    csp
    co
    #
    cabs
    cfv
    #
    wceq
    #
    @55
    @10
    @56
    cc
    wcel
    #
    @0
    @58
    @10
    @3
    @0
    @3
    cc
    wcel
    @9
    @0
    @3
    @36
    recnd
    #
    adantr
    #
    @0
    @3
    cc0
    wne
    @9
    cA
    normne0
    biimpar
    #
    reccld
    #
    @0
    @9
    simpl
    #
    @56
    cA
    hvmulcl
    syl2anc
    @10
    @59
    c1
    c1
    cle
    cA
    norm1
    1le1
    syl6eqbr
    @10
    @61
    @56
    cA
    cA
    csp
    co
    #
    cmul
    co
    #
    @62
    @3
    @10
    @64
    @0
    @0
    @61
    @71
    wceq
    @68
    @69
    @69
    @56
    cA
    cA
    ax-his3
    syl3anc
    #
    @10
    @61
    @10
    @61
    @71
    cr
    @72
    @10
    @56
    @70
    @10
    @3
    @0
    @3
    cr
    wcel
    @9
    @36
    adantr
    #
    @67
    rereccld
    #
    @0
    @70
    cr
    wcel
    @9
    cA
    hiidrcl
    adantr
    #
    remulcld
    eqeltrd
    @10
    cc0
    @71
    @61
    cle
    @10
    @56
    @70
    @74
    @75
    @10
    @56
    cr
    wcel
    #
    cc0
    @56
    clt
    wbr
    #
    cc0
    @56
    cle
    wbr
    #
    @74
    @10
    @3
    @73
    @0
    @9
    cc0
    @3
    clt
    wbr
    cA
    normgt0
    biimpa
    recgt0d
    cc0
    cr
    wcel
    @76
    @77
    @78
    wi
    0re
    cc0
    @56
    ltle
    mpan
    sylc
    @0
    cc0
    @70
    cle
    wbr
    @9
    cA
    hiidge0
    adantr
    mulge0d
    @72
    breqtrrd
    absidd
    @10
    @3
    @56
    @3
    cmul
    co
    #
    cmul
    co
    #
    @3
    c1
    cmul
    co
    #
    @71
    @3
    @10
    @79
    c1
    @3
    cmul
    @10
    @3
    @66
    @67
    recid2d
    oveq2d
    @10
    @80
    @56
    @3
    @3
    cmul
    co
    #
    cmul
    co
    @71
    @10
    @3
    @56
    @3
    @66
    @68
    @66
    mul12d
    @10
    @82
    @70
    @56
    cmul
    @0
    @82
    @70
    wceq
    @9
    @0
    @3
    c2
    cexp
    co
    @82
    @70
    @0
    @3
    @65
    sqvald
    cA
    normsq
    eqtr3d
    adantr
    oveq2d
    eqtrd
    @0
    @81
    @3
    wceq
    @9
    @0
    @3
    @65
    mulid1d
    adantr
    3eqtr3rd
    3eqtr4rd
    @54
    @60
    @63
    wa
    vy
    @57
    chil
    @11
    @57
    wceq
    #
    @13
    @60
    @53
    @63
    @83
    @12
    @59
    c1
    cle
    @11
    @57
    cno
    fveq2
    breq1d
    @83
    @45
    @62
    @3
    @83
    @44
    @61
    cabs
    @11
    @57
    cA
    csp
    oveq1
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    @0
    @52
    @55
    wb
    @9
    @0
    @51
    @54
    vy
    chil
    @42
    @50
    @53
    @13
    @42
    @16
    @45
    @3
    @46
    eqeq2d
    anbi2d
    rexbidva
    adantr
    mpbird
    @19
    @52
    vx
    @3
    cA
    cno
    fvex
    @14
    @3
    wceq
    #
    @18
    @51
    vy
    chil
    @84
    @17
    @50
    @13
    @14
    @3
    @16
    eqeq1
    anbi2d
    rexbidv
    elab
    sylibr
    @33
    @31
    vw
    @3
    @20
    @32
    @3
    @28
    clt
    breq2
    rspcev
    sylan
    adantlr
    ex
    ralrimiva
    vz
    vw
    @20
    @3
    supxr2
    syl12anc
    eqtrd
    @7
    @0
    chil
    cc0
    csn
    cxp
    #
    cnmf
    cfv
    cc0
    @5
    @6
    nmfn0
    @4
    @85
    cnmf
    bra0
    fveq2i
    norm0
    3eqtr4i
    a1i
    pm2.61ne
end
