include "wcel.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "cgrp.mm"
include "cv.mm"
include "csubg.mm"
include "cfv.mm"
include "wf.mm"
include "wss.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cima.mm"
include "cuni.mm"
include "cin.mm"
include "cab.mm"
include "cdprd.mm"
include "wbr.mm"
include "w3a.mm"
include "cvv.mm"
include "wi.mm"
include "elex.mm"
include "a1i.mm"
include "fex.mm"
include "expcom.mm"
include "adantr.mm"
include "adantrd.mm"
include "wb.mm"
include "wsbc.mm"
include "df-sbc.mm"
include "simpr.mm"
include "dmeqd.mm"
include "simplr.mm"
include "eqtrd.mm"
include "feq12d.mm"
include "difeq1d.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "raleqbidv.mm"
include "imaeq12d.mm"
include "unieqd.mm"
include "ineq12d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "adantlr.mm"
include "sbcied.mm"
include "syl5bbr.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "anbi2d.mm"
include "cop.mm"
include "ccntz.mm"
include "cmrc.mm"
include "c0g.mm"
include "cxp.mm"
include "ciun.mm"
include "df-br.mm"
include "cfsupp.mm"
include "cixp.mm"
include "crab.mm"
include "cgsu.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "fvex.mm"
include "rgenw.mm"
include "ixpexg.mm"
include "ax-mp.mm"
include "mptrabex.mm"
include "rnex.mm"
include "rgen2w.mm"
include "df-dprd.mm"
include "fmpt2x.mm"
include "mpbi.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "fveq2.mm"
include "feq3d.mm"
include "syl6eqr.mm"
include "sseq2d.mm"
include "ralbidv.mm"
include "ineq2d.mm"
include "sneqd.mm"
include "eqeq12d.mm"
include "abbidv.mm"
include "opeliunxp2.mm"
include "3bitri.mm"
include "3anass.mm"
include "3bitr4g.mm"

theorem dmdprd
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cG: class G
  let cI: class I
  let cK: class K
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  let vg: setvar g
  let vh: setvar h
  let vf: setvar f
  let vi: setvar i
  let vs: setvar s
  let wph: wff ph
  assume dmdprd.z: |- Z = ( Cntz ` G )
  assume dmdprd.0: |- .0. = ( 0g ` G )
  assume dmdprd.k: |- K = ( mrCls ` ( SubGrp ` G ) )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint I x
  disjoint I y
  disjoint S x
  disjoint S y
  disjoint V x
  disjoint V y
  disjoint g h
  disjoint .0. g
  disjoint .0. h
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint G f
  disjoint g i
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint G g
  disjoint h i
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint G h
  disjoint i s
  disjoint i x
  disjoint i y
  disjoint G i
  disjoint s x
  disjoint s y
  disjoint G s
  disjoint I h
  disjoint K g
  disjoint K h
  disjoint Z g
  disjoint Z h
  disjoint ph x
  disjoint ph y
  disjoint S g
  disjoint S h
  disjoint V h
  assert |- ( ( I e. V /\ dom S = I ) -> ( G dom DProd S <-> ( G e. Grp /\ S : I --> ( SubGrp ` G ) /\ A. x e. I ( A. y e. ( I \ { x } ) ( S ` x ) C_ ( Z ` ( S ` y ) ) /\ ( ( S ` x ) i^i ( K ` U. ( S " ( I \ { x } ) ) ) ) = { .0. } ) ) ) )

  proof
    cI
    cV
    wcel
    #
    cS
    cdm
    #
    cI
    wceq
    #
    wa
    #
    cG
    cgrp
    wcel
    #
    cS
    vh
    cv
    #
    cdm
    #
    cG
    csubg
    cfv
    #
    @5
    wf
    #
    vx
    cv
    #
    @5
    cfv
    #
    vy
    cv
    #
    @5
    cfv
    #
    cZ
    cfv
    #
    wss
    #
    vy
    @6
    @9
    csn
    #
    cdif
    #
    wral
    #
    @10
    @5
    @16
    cima
    #
    cuni
    #
    cK
    cfv
    #
    cin
    #
    c.0
    csn
    #
    wceq
    #
    wa
    #
    vx
    @6
    wral
    #
    wa
    #
    vh
    cab
    #
    wcel
    #
    wa
    #
    @4
    cI
    @7
    cS
    wf
    #
    @9
    cS
    cfv
    #
    @11
    cS
    cfv
    #
    cZ
    cfv
    #
    wss
    #
    vy
    cI
    @15
    cdif
    #
    wral
    #
    @31
    cS
    @35
    cima
    #
    cuni
    #
    cK
    cfv
    #
    cin
    #
    @22
    wceq
    #
    wa
    #
    vx
    cI
    wral
    #
    wa
    #
    wa
    cG
    cS
    cdprd
    cdm
    #
    wbr
    #
    @4
    @30
    @43
    w3a
    @3
    @28
    @44
    @4
    @3
    cS
    cvv
    wcel
    #
    @28
    @44
    @28
    @47
    wi
    @3
    cS
    @27
    elex
    a1i
    @3
    @30
    @47
    @43
    @0
    @30
    @47
    wi
    @2
    @30
    @0
    @47
    cI
    @7
    cV
    cS
    fex
    expcom
    adantr
    adantrd
    @3
    @47
    @28
    @44
    wb
    @28
    @26
    vh
    cS
    wsbc
    @3
    @47
    wa
    #
    @44
    @26
    vh
    cS
    df-sbc
    @48
    @26
    @44
    vh
    cS
    cvv
    @3
    @47
    simpr
    @3
    @5
    cS
    wceq
    #
    @26
    @44
    wb
    @47
    @3
    @49
    wa
    #
    @8
    @30
    @25
    @43
    @50
    @6
    cI
    @7
    @5
    cS
    @3
    @49
    simpr
    #
    @50
    @6
    @1
    cI
    @50
    @5
    cS
    @51
    dmeqd
    @0
    @2
    @49
    simplr
    eqtrd
    #
    feq12d
    @50
    @24
    @42
    vx
    @6
    cI
    @52
    @50
    @17
    @36
    @23
    @41
    @50
    @14
    @34
    vy
    @16
    @35
    @50
    @6
    cI
    @15
    @52
    difeq1d
    #
    @50
    @10
    @31
    @13
    @33
    @50
    @9
    @5
    cS
    @51
    fveq1d
    #
    @50
    @12
    @32
    cZ
    @50
    @11
    @5
    cS
    @51
    fveq1d
    fveq2d
    sseq12d
    raleqbidv
    @50
    @21
    @40
    @22
    @50
    @10
    @31
    @20
    @39
    @54
    @50
    @19
    @38
    cK
    @50
    @18
    @37
    @50
    @5
    cS
    @16
    @35
    @51
    @53
    imaeq12d
    unieqd
    fveq2d
    ineq12d
    eqeq1d
    anbi12d
    raleqbidv
    anbi12d
    adantlr
    sbcied
    syl5bbr
    ex
    pm5.21ndd
    anbi2d
    @46
    cG
    cS
    cop
    #
    @45
    wcel
    @55
    vg
    cgrp
    vg
    cv
    #
    csn
    @6
    @56
    csubg
    cfv
    #
    @5
    wf
    #
    @10
    @12
    @56
    ccntz
    cfv
    #
    cfv
    #
    wss
    #
    vy
    @16
    wral
    #
    @10
    @19
    @57
    cmrc
    cfv
    #
    cfv
    #
    cin
    #
    @56
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    wa
    #
    vx
    @6
    wral
    #
    wa
    #
    vh
    cab
    #
    cxp
    ciun
    #
    wcel
    @29
    cG
    cS
    @45
    df-br
    @45
    @73
    @55
    @73
    cvv
    cdprd
    vf
    @5
    @66
    cfsupp
    wbr
    #
    vh
    vx
    vs
    cv
    #
    cdm
    #
    @9
    @75
    cfv
    #
    cixp
    #
    crab
    @56
    vf
    cv
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    cvv
    wcel
    #
    vs
    @72
    wral
    vg
    cgrp
    wral
    @73
    cvv
    cdprd
    wf
    @82
    vg
    vs
    cgrp
    @72
    @80
    @74
    vf
    vh
    @78
    @79
    @77
    cvv
    wcel
    #
    vx
    @76
    wral
    @78
    cvv
    wcel
    @83
    vx
    @76
    @9
    @75
    fvex
    rgenw
    vx
    @76
    @77
    cvv
    ixpexg
    ax-mp
    mptrabex
    rnex
    rgen2w
    vg
    vs
    cgrp
    @72
    @81
    cvv
    cdprd
    vx
    vy
    vf
    vg
    vh
    vs
    df-dprd
    fmpt2x
    mpbi
    fdmi
    eleq2i
    vg
    cgrp
    @72
    cG
    cS
    @27
    @56
    cG
    wceq
    #
    @71
    @26
    vh
    @84
    @58
    @8
    @70
    @25
    @84
    @57
    @7
    @5
    @6
    @56
    cG
    csubg
    fveq2
    #
    feq3d
    @84
    @69
    @24
    vx
    @6
    @84
    @62
    @17
    @68
    @23
    @84
    @61
    @14
    vy
    @16
    @84
    @60
    @13
    @10
    @84
    @12
    @59
    cZ
    @84
    @59
    cG
    ccntz
    cfv
    cZ
    @56
    cG
    ccntz
    fveq2
    dmdprd.z
    syl6eqr
    fveq1d
    sseq2d
    ralbidv
    @84
    @65
    @21
    @67
    @22
    @84
    @64
    @20
    @10
    @84
    @19
    @63
    cK
    @84
    @63
    @7
    cmrc
    cfv
    cK
    @84
    @57
    @7
    cmrc
    @85
    fveq2d
    dmdprd.k
    syl6eqr
    fveq1d
    ineq2d
    @84
    @66
    c.0
    @84
    @66
    cG
    c0g
    cfv
    c.0
    @56
    cG
    c0g
    fveq2
    dmdprd.0
    syl6eqr
    sneqd
    eqeq12d
    anbi12d
    ralbidv
    anbi12d
    abbidv
    opeliunxp2
    3bitri
    @4
    @30
    @43
    3anass
    3bitr4g
end
