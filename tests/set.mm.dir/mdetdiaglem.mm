include "ccrg.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cid.mm"
include "cres.mm"
include "wa.mm"
include "ccom.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "czrh.mm"
include "cpsgn.mm"
include "a1i.mm"
include "coeq12d.mm"
include "fveq1d.mm"
include "cdif.mm"
include "cdm.mm"
include "c0.mm"
include "wb.mm"
include "wfn.mm"
include "wf1o.mm"
include "csymg.mm"
include "eqid.mm"
include "symgbasf1o.mm"
include "f1ofn.mm"
include "syl.mm"
include "fnnfpeq0.mm"
include "adantl.mm"
include "bicomd.mm"
include "necon3bid.mm"
include "wex.mm"
include "n0.mm"
include "csn.mm"
include "cmulr.mm"
include "cbs.mm"
include "mgpplusg.mm"
include "ccmn.mm"
include "crngmgp.mm"
include "3ad2ant1.mm"
include "ad2antrr.mm"
include "simpll2.mm"
include "cxp.mm"
include "wf.mm"
include "cmap.mm"
include "matbas2i.mm"
include "3ad2ant3.mm"
include "elmapi.mm"
include "mgpbas.mm"
include "eqcomi.mm"
include "feq3d.mm"
include "mpbird.mm"
include "ad3antrrr.mm"
include "symgbasf.mm"
include "ad2antrl.mm"
include "ffvelrnda.mm"
include "simpr.mm"
include "fovrnd.mm"
include "cin.mm"
include "disjdif.mm"
include "cun.mm"
include "wss.mm"
include "difss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "sseld.mm"
include "impr.mm"
include "snssd.mm"
include "undif.mm"
include "sylib.mm"
include "eqcomd.mm"
include "gsummptfidmsplit.mm"
include "cmnd.mm"
include "cvv.mm"
include "crg.mm"
include "crngring.mm"
include "adantr.mm"
include "ringmgp.mm"
include "3adant3.mm"
include "vex.mm"
include "ffvelrnd.mm"
include "weq.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "gsumsn.mm"
include "syl3anc.mm"
include "simprr.mm"
include "fnelnfp.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "neeq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "neeq2.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "impancom.mm"
include "imp.mm"
include "mpd.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "simpl2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "eldifi.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "ad2ant2r.mm"
include "ringlz.mm"
include "3eqtrd.mm"
include "expr.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "expimpd.mm"
include "3impia.mm"
include "3simpa.mm"
include "simpl.mm"
include "cmgp.mm"
include "cmhm.mm"
include "zrhpsgnmhm.mm"
include "sylan.mm"
include "mhmf.mm"
include "ringrz.mm"
include "syl2an.mm"
include "3adant2.mm"

theorem mdetdiaglem
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  assume mdetdiag.d: |- D = ( N maDet R )
  assume mdetdiag.a: |- A = ( N Mat R )
  assume mdetdiag.b: |- B = ( Base ` A )
  assume mdetdiag.g: |- G = ( mulGrp ` R )
  assume mdetdiag.0: |- .0. = ( 0g ` R )
  assume mdetdiaglem.g: |- H = ( Base ` ( SymGrp ` N ) )
  assume mdetdiaglem.z: |- Z = ( ZRHom ` R )
  assume mdetdiaglem.s: |- S = ( pmSgn ` N )
  assume mdetdiaglem.t: |- .x. = ( .r ` R )

  disjoint B k
  disjoint G k
  disjoint H k
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint P i
  disjoint P j
  disjoint P k
  disjoint R k
  disjoint .0. i
  disjoint .0. j
  disjoint .0. k
  disjoint B s
  disjoint k s
  disjoint G s
  disjoint H s
  disjoint M s
  disjoint i s
  disjoint j s
  disjoint N s
  disjoint P s
  disjoint R s
  disjoint .0. s
  assert |- ( ( ( R e. CRing /\ N e. Fin /\ M e. B ) /\ A. i e. N A. j e. N ( i =/= j -> ( i M j ) = .0. ) /\ ( P e. H /\ P =/= ( _I |` N ) ) ) -> ( ( ( Z o. S ) ` P ) .x. ( G gsum ( k e. N |-> ( ( P ` k ) M k ) ) ) ) = .0. )

  proof
    cR
    ccrg
    wcel
    #
    cN
    cfn
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vi
    cv
    #
    vj
    cv
    #
    wne
    #
    @4
    @5
    cM
    co
    #
    c.0
    wceq
    #
    wi
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    cP
    cH
    wcel
    #
    cP
    cid
    cN
    cres
    #
    wne
    #
    wa
    #
    w3a
    #
    cP
    cZ
    cS
    ccom
    #
    cfv
    #
    cG
    vk
    cN
    vk
    cv
    #
    cP
    cfv
    #
    @18
    cM
    co
    #
    cmpt
    cgsu
    co
    #
    c.x
    co
    cP
    cR
    czrh
    cfv
    #
    cN
    cpsgn
    cfv
    #
    ccom
    #
    cfv
    #
    c.0
    c.x
    co
    #
    c.0
    @15
    @17
    @25
    @21
    c.0
    c.x
    @15
    cP
    @16
    @24
    @15
    cZ
    @22
    cS
    @23
    cZ
    @22
    wceq
    @15
    mdetdiaglem.z
    a1i
    cS
    @23
    wceq
    @15
    mdetdiaglem.s
    a1i
    coeq12d
    fveq1d
    @3
    @10
    @14
    @21
    c.0
    wceq
    #
    @3
    @10
    wa
    #
    @11
    @13
    @27
    @28
    @11
    wa
    #
    @13
    cP
    cid
    cdif
    #
    cdm
    #
    c0
    wne
    #
    @27
    @29
    cP
    @12
    @31
    c0
    @29
    @31
    c0
    wceq
    #
    cP
    @12
    wceq
    #
    @11
    @33
    @34
    wb
    #
    @28
    @11
    cP
    cN
    wfn
    #
    @35
    @11
    cN
    cN
    cP
    wf1o
    @36
    cN
    cH
    cP
    cN
    csymg
    cfv
    #
    @37
    eqid
    #
    mdetdiaglem.g
    symgbasf1o
    cN
    cN
    cP
    f1ofn
    syl
    #
    cN
    cP
    fnnfpeq0
    syl
    adantl
    bicomd
    necon3bid
    @32
    vs
    cv
    #
    @31
    wcel
    #
    vs
    wex
    @29
    @27
    vs
    @31
    n0
    @29
    @41
    @27
    vs
    @28
    @11
    @41
    @27
    @28
    @11
    @41
    wa
    #
    wa
    #
    @21
    cG
    vk
    @40
    csn
    #
    @20
    cmpt
    cgsu
    co
    #
    cG
    vk
    cN
    @44
    cdif
    #
    @20
    cmpt
    cgsu
    co
    #
    cR
    cmulr
    cfv
    #
    co
    c.0
    @47
    @48
    co
    #
    c.0
    @43
    cN
    cG
    cbs
    cfv
    #
    @44
    @46
    @48
    vk
    cG
    @20
    @50
    eqid
    cR
    @48
    cG
    mdetdiag.g
    @48
    eqid
    #
    mgpplusg
    @3
    cG
    ccmn
    wcel
    #
    @10
    @42
    @0
    @1
    @52
    @2
    cR
    cG
    mdetdiag.g
    crngmgp
    3ad2ant1
    #
    ad2antrr
    @0
    @1
    @2
    @10
    @42
    simpll2
    @43
    @18
    cN
    wcel
    #
    wa
    @19
    @18
    @50
    cN
    cN
    cM
    @3
    cN
    cN
    cxp
    #
    @50
    cM
    wf
    #
    @10
    @42
    @54
    @3
    @56
    @55
    cR
    cbs
    cfv
    #
    cM
    wf
    #
    @3
    cM
    @57
    @55
    cmap
    co
    wcel
    #
    @58
    @2
    @0
    @59
    @1
    cA
    cB
    cR
    @57
    cM
    cN
    mdetdiag.a
    @57
    eqid
    #
    mdetdiag.b
    matbas2i
    3ad2ant3
    cM
    @57
    @55
    elmapi
    syl
    #
    @3
    @50
    @57
    cM
    @55
    @50
    @57
    wceq
    @3
    @57
    @50
    @57
    cR
    cG
    mdetdiag.g
    @60
    mgpbas
    #
    eqcomi
    a1i
    feq3d
    mpbird
    ad3antrrr
    @43
    cN
    cN
    @18
    cP
    @11
    cN
    cN
    cP
    wf
    #
    @28
    @41
    cN
    cH
    cP
    @37
    @38
    mdetdiaglem.g
    symgbasf
    #
    ad2antrl
    #
    ffvelrnda
    @43
    @54
    simpr
    fovrnd
    @44
    @46
    cin
    c0
    wceq
    @43
    @44
    cN
    disjdif
    a1i
    @43
    @44
    @46
    cun
    #
    cN
    @43
    @44
    cN
    wss
    @66
    cN
    wceq
    @43
    @40
    cN
    @28
    @11
    @41
    @40
    cN
    wcel
    #
    @29
    @31
    cN
    @40
    @29
    cP
    cdm
    #
    @31
    cN
    @30
    cP
    wss
    @31
    @68
    wss
    cP
    cid
    difss
    @30
    cP
    dmss
    ax-mp
    #
    @29
    @63
    @68
    cN
    wceq
    #
    @11
    @63
    @28
    @64
    adantl
    cN
    cN
    cP
    fdm
    #
    syl
    syl5sseq
    sseld
    impr
    #
    snssd
    @44
    cN
    undif
    sylib
    eqcomd
    gsummptfidmsplit
    @43
    @45
    c.0
    @47
    @48
    @43
    @45
    @40
    cP
    cfv
    #
    @40
    cM
    co
    #
    c.0
    @43
    cG
    cmnd
    wcel
    #
    @40
    cvv
    wcel
    #
    @74
    @57
    wcel
    @45
    @74
    wceq
    @3
    @75
    @10
    @42
    @0
    @1
    @75
    @2
    @0
    @1
    wa
    #
    cR
    crg
    wcel
    #
    @75
    @0
    @78
    @1
    cR
    crngring
    #
    adantr
    cR
    cG
    mdetdiag.g
    ringmgp
    syl
    3adant3
    ad2antrr
    @76
    @43
    vs
    vex
    a1i
    @43
    @73
    @40
    @57
    cN
    cN
    cM
    @3
    @58
    @10
    @42
    @61
    ad2antrr
    @43
    cN
    cN
    @40
    cP
    @65
    @72
    ffvelrnd
    @72
    fovrnd
    @20
    @57
    @74
    vk
    cG
    @40
    cvv
    @62
    vk
    vs
    weq
    #
    @19
    @73
    @18
    @40
    cM
    @18
    @40
    cP
    fveq2
    @80
    id
    oveq12d
    gsumsn
    syl3anc
    @43
    @73
    @40
    wne
    #
    @74
    c.0
    wceq
    #
    @43
    @41
    @81
    @28
    @11
    @41
    simprr
    @43
    @36
    @67
    @41
    @81
    wb
    @11
    @36
    @28
    @41
    @39
    ad2antrl
    @72
    cN
    cP
    @40
    fnelnfp
    syl2anc
    mpbid
    @28
    @42
    @81
    @82
    wi
    #
    @3
    @42
    @10
    @83
    @3
    @42
    wa
    #
    @73
    cN
    wcel
    @67
    @10
    @83
    wi
    @84
    cN
    cN
    @40
    cP
    @11
    @63
    @3
    @41
    @64
    ad2antrl
    @3
    @11
    @41
    @67
    @3
    @11
    wa
    #
    @31
    cN
    @40
    @85
    @68
    @31
    cN
    @69
    @85
    @63
    @70
    @11
    @63
    @3
    @64
    adantl
    #
    @71
    syl
    syl5sseq
    sseld
    impr
    #
    ffvelrnd
    @87
    @9
    @83
    @73
    @5
    wne
    #
    @73
    @5
    cM
    co
    #
    c.0
    wceq
    #
    wi
    vi
    vj
    @73
    @40
    cN
    cN
    @4
    @73
    wceq
    #
    @6
    @88
    @8
    @90
    @4
    @73
    @5
    neeq1
    @91
    @7
    @89
    c.0
    @4
    @73
    @5
    cM
    oveq1
    eqeq1d
    imbi12d
    vj
    vs
    weq
    #
    @88
    @81
    @90
    @82
    @5
    @40
    @73
    neeq2
    @92
    @89
    @74
    c.0
    @5
    @40
    @73
    cM
    oveq2
    eqeq1d
    imbi12d
    rspc2v
    syl2anc
    impancom
    imp
    mpd
    eqtrd
    oveq1d
    @43
    @78
    @47
    @57
    wcel
    #
    @49
    c.0
    wceq
    @3
    @78
    @10
    @42
    @0
    @1
    @78
    @2
    @79
    3ad2ant1
    ad2antrr
    @3
    @11
    @93
    @10
    @41
    @85
    @57
    vk
    cG
    @46
    @20
    @62
    @3
    @52
    @11
    @53
    adantr
    @85
    @1
    @46
    cN
    wss
    @46
    cfn
    wcel
    @0
    @1
    @2
    @11
    simpl2
    cN
    @44
    difss
    cN
    @46
    ssfi
    sylancl
    @85
    @20
    @57
    wcel
    vk
    @46
    @85
    @18
    @46
    wcel
    #
    wa
    #
    @19
    @18
    @57
    cN
    cN
    cM
    @3
    @58
    @11
    @94
    @61
    ad2antrr
    @95
    cN
    cN
    @18
    cP
    @85
    @63
    @94
    @86
    adantr
    @94
    @54
    @85
    @18
    cN
    @44
    eldifi
    adantl
    #
    ffvelrnd
    @96
    fovrnd
    ralrimiva
    gsummptcl
    ad2ant2r
    @57
    cR
    @48
    @47
    c.0
    @60
    @51
    mdetdiag.0
    ringlz
    syl2anc
    3eqtrd
    expr
    exlimdv
    syl5bi
    sylbid
    expimpd
    3impia
    oveq12d
    @3
    @14
    @26
    c.0
    wceq
    #
    @10
    @3
    @77
    @11
    @97
    @14
    @0
    @1
    @2
    3simpa
    @11
    @13
    simpl
    @77
    @11
    wa
    @78
    @25
    cR
    cmgp
    cfv
    #
    cbs
    cfv
    #
    wcel
    @97
    @0
    @78
    @1
    @11
    @79
    ad2antrr
    @77
    cH
    @99
    cP
    @24
    @77
    @24
    @37
    @98
    cmhm
    co
    wcel
    #
    cH
    @99
    @24
    wf
    @0
    @78
    @1
    @100
    @79
    cN
    cR
    zrhpsgnmhm
    sylan
    cH
    @99
    @37
    @98
    @24
    mdetdiaglem.g
    @99
    eqid
    mhmf
    syl
    ffvelrnda
    @99
    cR
    c.x
    @25
    c.0
    @57
    @99
    @57
    cR
    @98
    @98
    eqid
    @60
    mgpbas
    eqcomi
    mdetdiaglem.t
    mdetdiag.0
    ringrz
    syl2anc
    syl2an
    3adant2
    eqtrd
end
