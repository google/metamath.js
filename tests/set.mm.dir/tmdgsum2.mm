include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "wcel.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "cdif.mm"
include "cfn.mm"
include "wrex.mm"
include "w3a.mm"
include "cixp.mm"
include "wa.mm"
include "wex.mm"
include "cgsu.mm"
include "co.mm"
include "cmap.mm"
include "crab.mm"
include "wss.mm"
include "cab.mm"
include "ctg.mm"
include "cpw.mm"
include "cxko.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "eqid.mm"
include "mptpreima.mm"
include "ccn.mm"
include "ccmn.mm"
include "ctmd.mm"
include "tmdgsum.mm"
include "syl3anc.mm"
include "cnima.mm"
include "syl2anc.mm"
include "syl5eqelr.mm"
include "cpt.mm"
include "ctop.mm"
include "ctopon.mm"
include "tmdtopon.mm"
include "topontop.mm"
include "3syl.mm"
include "xkopt.mm"
include "fnconstg.mm"
include "ptval.mm"
include "eqtrd.mm"
include "eleqtrd.mm"
include "wf.mm"
include "fconst6g.mm"
include "syl.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "chash.mm"
include "fconstmpt.mm"
include "oveq2i.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "gsumconst.mm"
include "syl5eq.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "tg2.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rexab2.mm"
include "sylib.mm"
include "wi.mm"
include "crn.mm"
include "cint.mm"
include "cin.mm"
include "toponuni.mm"
include "ad2antrr.mm"
include "ineq1d.mm"
include "simplrl.mm"
include "simplrr.mm"
include "fvconst2g.mm"
include "eleq2d.mm"
include "ralbidva.mm"
include "mpbid.mm"
include "ffnfv.mm"
include "frn.mm"
include "wfo.mm"
include "dffn4.mm"
include "fofi.mm"
include "rintopn.mm"
include "simprl.mm"
include "mptelixpg.mm"
include "ralrn.mm"
include "elrint.mm"
include "inex1.mm"
include "ixpconstg.mm"
include "sylancl.mm"
include "inss2.mm"
include "fnfvelrn.mm"
include "intss1.mm"
include "syl5ss.mm"
include "ralrimiva.mm"
include "ss2ixp.mm"
include "eqsstr3d.mm"
include "ssrab.mm"
include "simprbi.mm"
include "ad2antll.mm"
include "ssralv.mm"
include "sylc.mm"
include "oveq1.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ex.mm"
include "3adantr3.mm"
include "imbi1d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "impd.mm"
include "mpd.mm"

theorem tmdgsum2
  let wph: wff ph
  let vu: setvar u
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let cG: class G
  let cJ: class J
  let cX: class X
  let vg: setvar g
  let vk: setvar k
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tmdgsum.j: |- J = ( TopOpen ` G )
  assume tmdgsum.b: |- B = ( Base ` G )
  assume tmdgsum2.t: |- .x. = ( .g ` G )
  assume tmdgsum2.1: |- ( ph -> G e. CMnd )
  assume tmdgsum2.2: |- ( ph -> G e. TopMnd )
  assume tmdgsum2.a: |- ( ph -> A e. Fin )
  assume tmdgsum2.u: |- ( ph -> U e. J )
  assume tmdgsum2.x: |- ( ph -> X e. B )
  assume tmdgsum2.3: |- ( ph -> ( ( # ` A ) .x. X ) e. U )

  disjoint f u
  disjoint A f
  disjoint A u
  disjoint J f
  disjoint J u
  disjoint X f
  disjoint X u
  disjoint B f
  disjoint B u
  disjoint G f
  disjoint G u
  disjoint U f
  disjoint U u
  disjoint f g
  disjoint f k
  disjoint f t
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g t
  disjoint g u
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k t
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint J g
  disjoint J t
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint X g
  disjoint X k
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint B g
  disjoint B k
  disjoint B t
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint G g
  disjoint G k
  disjoint G t
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint U g
  disjoint U t
  disjoint U x
  disjoint g ph
  disjoint ph x
  assert |- ( ph -> E. u e. J ( X e. u /\ A. f e. ( u ^m A ) ( G gsum f ) e. U ) )

  proof
    wph
    vg
    cv
    #
    cA
    wfn
    #
    vy
    cv
    #
    @0
    cfv
    #
    @2
    cA
    cJ
    csn
    cxp
    #
    cfv
    #
    wcel
    #
    vy
    cA
    wral
    #
    @3
    @5
    cuni
    wceq
    vy
    cA
    vz
    cv
    #
    cdif
    wral
    vz
    cfn
    wrex
    #
    w3a
    #
    vx
    cv
    #
    vy
    cA
    @3
    cixp
    #
    wceq
    #
    wa
    #
    vg
    wex
    #
    cA
    cX
    csn
    cxp
    #
    @11
    wcel
    #
    @11
    cG
    vf
    cv
    #
    cgsu
    co
    #
    cU
    wcel
    #
    vf
    cB
    cA
    cmap
    co
    #
    crab
    #
    wss
    #
    wa
    #
    wa
    #
    vx
    wex
    #
    cX
    vu
    cv
    #
    wcel
    #
    @20
    vf
    @27
    cA
    cmap
    co
    #
    wral
    #
    wa
    #
    vu
    cJ
    wrex
    #
    wph
    @16
    vt
    cv
    #
    wcel
    #
    @33
    @22
    wss
    #
    wa
    #
    vt
    @15
    vx
    cab
    #
    wrex
    #
    @26
    wph
    @22
    @37
    ctg
    cfv
    #
    wcel
    @16
    @22
    wcel
    #
    @38
    wph
    @22
    cJ
    cA
    cpw
    cxko
    co
    #
    @39
    wph
    @22
    vf
    @21
    @19
    cmpt
    #
    ccnv
    cU
    cima
    #
    @41
    vf
    @21
    @19
    cU
    @42
    @42
    eqid
    mptpreima
    wph
    @42
    @41
    cJ
    ccn
    co
    wcel
    #
    cU
    cJ
    wcel
    @43
    @41
    wcel
    wph
    cG
    ccmn
    wcel
    #
    cG
    ctmd
    wcel
    #
    cA
    cfn
    wcel
    #
    @44
    tmdgsum2.1
    tmdgsum2.2
    tmdgsum2.a
    vf
    cA
    cB
    cG
    cJ
    tmdgsum.j
    tmdgsum.b
    tmdgsum
    syl3anc
    tmdgsum2.u
    cU
    @42
    @41
    cJ
    cnima
    syl2anc
    syl5eqelr
    wph
    @41
    @4
    cpt
    cfv
    #
    @39
    wph
    cJ
    ctop
    wcel
    #
    @47
    @41
    @48
    wceq
    wph
    @46
    cJ
    cB
    ctopon
    cfv
    #
    wcel
    #
    @49
    tmdgsum2.2
    cG
    cJ
    cB
    tmdgsum.j
    tmdgsum.b
    tmdtopon
    #
    cB
    cJ
    topontop
    3syl
    #
    tmdgsum2.a
    cA
    cJ
    cfn
    xkopt
    syl2anc
    wph
    @47
    @4
    cA
    wfn
    #
    @48
    @39
    wceq
    tmdgsum2.a
    wph
    @46
    @51
    @54
    tmdgsum2.2
    @52
    cA
    cJ
    @50
    fnconstg
    3syl
    vx
    vy
    vz
    cA
    @37
    vg
    @4
    cfn
    @37
    eqid
    ptval
    syl2anc
    eqtrd
    eleqtrd
    wph
    @16
    @21
    wcel
    #
    cG
    @16
    cgsu
    co
    #
    cU
    wcel
    #
    @40
    wph
    @55
    cA
    cB
    @16
    wf
    #
    wph
    cX
    cB
    wcel
    #
    @58
    tmdgsum2.x
    cA
    cX
    cB
    fconst6g
    syl
    wph
    cB
    cvv
    wcel
    @47
    @55
    @58
    wb
    cB
    cG
    cbs
    cfv
    cvv
    tmdgsum.b
    cG
    cbs
    fvex
    eqeltri
    #
    tmdgsum2.a
    cB
    cA
    @16
    cvv
    cfn
    elmapg
    sylancr
    mpbird
    wph
    @56
    cA
    chash
    cfv
    cX
    c.x
    co
    #
    cU
    wph
    @56
    cG
    vk
    cA
    cX
    cmpt
    #
    cgsu
    co
    #
    @61
    @16
    @62
    cG
    cgsu
    vk
    cA
    cX
    fconstmpt
    oveq2i
    wph
    cG
    cmnd
    wcel
    #
    @47
    @59
    @63
    @61
    wceq
    wph
    @45
    @64
    tmdgsum2.1
    cG
    cmnmnd
    syl
    tmdgsum2.a
    tmdgsum2.x
    cA
    cB
    c.x
    vk
    cG
    cX
    tmdgsum.b
    tmdgsum2.t
    gsumconst
    syl3anc
    syl5eq
    tmdgsum2.3
    eqeltrd
    @20
    @57
    vf
    @16
    @21
    @18
    @16
    wceq
    @19
    @56
    cU
    @18
    @16
    cG
    cgsu
    oveq2
    eleq1d
    elrab
    sylanbrc
    vt
    @22
    @37
    @16
    tg2
    syl2anc
    @15
    @36
    @24
    vt
    vx
    @33
    @11
    wceq
    @34
    @17
    @35
    @23
    @33
    @11
    @16
    eleq2
    @33
    @11
    @22
    sseq1
    anbi12d
    rexab2
    sylib
    wph
    @25
    @32
    vx
    wph
    @15
    @24
    @32
    wph
    @14
    @24
    @32
    wi
    #
    vg
    wph
    @10
    @13
    @65
    wph
    @10
    wa
    @65
    @13
    @16
    @12
    wcel
    #
    @12
    @22
    wss
    #
    wa
    #
    @32
    wi
    #
    wph
    @1
    @7
    @69
    @9
    wph
    @1
    @7
    wa
    #
    wa
    #
    @68
    @32
    @71
    @68
    wa
    #
    cB
    @0
    crn
    #
    cint
    #
    cin
    #
    cJ
    wcel
    cX
    @75
    wcel
    #
    @20
    vf
    @75
    cA
    cmap
    co
    #
    wral
    #
    @32
    @72
    @75
    cJ
    cuni
    #
    @74
    cin
    #
    cJ
    @72
    cB
    @79
    @74
    wph
    cB
    @79
    wceq
    #
    @70
    @68
    wph
    @46
    @51
    @81
    tmdgsum2.2
    @52
    cB
    cJ
    toponuni
    3syl
    ad2antrr
    ineq1d
    @72
    @49
    @73
    cJ
    wss
    #
    @73
    cfn
    wcel
    #
    @80
    cJ
    wcel
    wph
    @49
    @70
    @68
    @53
    ad2antrr
    #
    @72
    cA
    cJ
    @0
    wf
    #
    @82
    @72
    @1
    @3
    cJ
    wcel
    #
    vy
    cA
    wral
    #
    @85
    wph
    @1
    @7
    @68
    simplrl
    #
    @72
    @7
    @87
    wph
    @1
    @7
    @68
    simplrr
    @72
    @49
    @7
    @87
    wb
    @84
    @49
    @6
    @86
    vy
    cA
    @49
    @2
    cA
    wcel
    #
    wa
    @5
    cJ
    @3
    cA
    cJ
    @2
    ctop
    fvconst2g
    eleq2d
    ralbidva
    syl
    mpbid
    vy
    cA
    cJ
    @0
    ffnfv
    sylanbrc
    cA
    cJ
    @0
    frn
    syl
    @72
    @47
    cA
    @73
    @0
    wfo
    #
    @83
    wph
    @47
    @70
    @68
    tmdgsum2.a
    ad2antrr
    #
    @72
    @1
    @90
    @88
    cA
    @0
    dffn4
    sylib
    cA
    @73
    @0
    fofi
    syl2anc
    @73
    cJ
    @79
    @79
    eqid
    rintopn
    syl3anc
    eqeltrd
    @72
    @59
    cX
    @8
    wcel
    #
    vz
    @73
    wral
    #
    @76
    wph
    @59
    @70
    @68
    tmdgsum2.x
    ad2antrr
    @72
    @93
    cX
    @3
    wcel
    #
    vy
    cA
    wral
    #
    @72
    vy
    cA
    cX
    cmpt
    #
    @12
    wcel
    #
    @95
    @72
    @96
    @16
    @12
    vy
    cA
    cX
    fconstmpt
    @71
    @66
    @67
    simprl
    syl5eqelr
    @72
    @47
    @97
    @95
    wb
    @91
    vy
    cA
    cX
    @3
    cfn
    mptelixpg
    syl
    mpbid
    @72
    @1
    @93
    @95
    wb
    @88
    @92
    @94
    vz
    vy
    cA
    @0
    @8
    @3
    cX
    eleq2
    ralrn
    syl
    mpbird
    vz
    cB
    @73
    cX
    elrint
    sylanbrc
    @72
    @77
    @12
    wss
    @20
    vf
    @12
    wral
    #
    @78
    @72
    @77
    vy
    cA
    @75
    cixp
    #
    @12
    @72
    @47
    @75
    cvv
    wcel
    @99
    @77
    wceq
    @91
    cB
    @74
    @60
    inex1
    vy
    cA
    @75
    cfn
    cvv
    ixpconstg
    sylancl
    @72
    @1
    @75
    @3
    wss
    #
    vy
    cA
    wral
    @99
    @12
    wss
    @88
    @1
    @100
    vy
    cA
    @1
    @89
    wa
    #
    @75
    @74
    @3
    cB
    @74
    inss2
    @101
    @3
    @73
    wcel
    @74
    @3
    wss
    cA
    @2
    @0
    fnfvelrn
    @3
    @73
    intss1
    syl
    syl5ss
    ralrimiva
    vy
    cA
    @75
    @3
    ss2ixp
    3syl
    eqsstr3d
    @67
    @98
    @71
    @66
    @67
    @12
    @21
    wss
    @98
    @20
    vf
    @21
    @12
    ssrab
    simprbi
    ad2antll
    @20
    vf
    @77
    @12
    ssralv
    sylc
    @31
    @76
    @78
    wa
    vu
    @75
    cJ
    @27
    @75
    wceq
    #
    @28
    @76
    @30
    @78
    @27
    @75
    cX
    eleq2
    @102
    @20
    vf
    @29
    @77
    @27
    @75
    cA
    cmap
    oveq1
    raleqdv
    anbi12d
    rspcev
    syl12anc
    ex
    3adantr3
    @13
    @24
    @68
    @32
    @13
    @17
    @66
    @23
    @67
    @11
    @12
    @16
    eleq2
    @11
    @12
    @22
    sseq1
    anbi12d
    imbi1d
    syl5ibrcom
    expimpd
    exlimdv
    impd
    exlimdv
    mpd
end
