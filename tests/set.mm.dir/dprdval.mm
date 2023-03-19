include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "cgsu.mm"
include "cmpt.mm"
include "crn.mm"
include "simpl.mm"
include "cfsupp.mm"
include "cfv.mm"
include "cixp.mm"
include "crab.mm"
include "wi.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "reldmdprd.mm"
include "brrelex2i.mm"
include "adantr.mm"
include "brrelexi.mm"
include "c0g.mm"
include "breq1.mm"
include "oveq1.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "cgrp.mm"
include "csubg.mm"
include "wf.mm"
include "ccntz.mm"
include "wss.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cima.mm"
include "cuni.mm"
include "cmrc.mm"
include "cin.mm"
include "cab.mm"
include "cop.mm"
include "cxp.mm"
include "ciun.mm"
include "df-br.mm"
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
include "opeliunxp.mm"
include "3bitri.mm"
include "ovmpt4g.mm"
include "mp3an3.mm"
include "sylbi.mm"
include "vtoclg.mm"
include "mpcom.mm"
include "sbcth.mm"
include "syl.mm"
include "simpr.mm"
include "oveq2d.mm"
include "dmeqd.mm"
include "simplr.mm"
include "eqtrd.mm"
include "ixpeq1d.mm"
include "fveq1d.mm"
include "ixpeq2dv.mm"
include "rabeqdv.mm"
include "eqidd.mm"
include "sbcied.mm"
include "mpbid.mm"
include "mpd.mm"

theorem dprdval
  let cS: class S
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let cG: class G
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let vg: setvar g
  let vs: setvar s
  let vy: setvar y
  let cA: class A
  assume dprdval.0: |- .0. = ( 0g ` G )
  assume dprdval.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }

  disjoint f h
  disjoint f i
  disjoint h i
  disjoint I f
  disjoint I h
  disjoint I i
  disjoint S f
  disjoint S h
  disjoint S i
  disjoint G f
  disjoint G h
  disjoint G i
  disjoint f g
  disjoint f s
  disjoint f y
  disjoint g h
  disjoint g i
  disjoint g s
  disjoint g y
  disjoint h s
  disjoint h y
  disjoint i s
  disjoint i y
  disjoint s y
  disjoint .0. g
  disjoint A f
  disjoint I s
  disjoint S s
  disjoint G g
  disjoint G s
  disjoint W s
  assert |- ( ( G dom DProd S /\ dom S = I ) -> ( G DProd S ) = ran ( f e. W |-> ( G gsum f ) ) )

  proof
    cG
    cS
    cdprd
    cdm
    #
    wbr
    #
    cS
    cdm
    #
    cI
    wceq
    #
    wa
    #
    @1
    cG
    cS
    cdprd
    co
    #
    vf
    cW
    cG
    vf
    cv
    #
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    wceq
    #
    @1
    @3
    simpl
    @4
    cG
    vs
    cv
    #
    @0
    wbr
    #
    cG
    @11
    cdprd
    co
    #
    vf
    vh
    cv
    #
    c.0
    cfsupp
    wbr
    #
    vh
    vi
    @11
    cdm
    #
    vi
    cv
    #
    @11
    cfv
    #
    cixp
    #
    crab
    #
    @7
    cmpt
    #
    crn
    #
    wceq
    #
    wi
    #
    vs
    cS
    wsbc
    #
    @1
    @10
    wi
    #
    @4
    cS
    cvv
    wcel
    #
    @25
    @1
    @27
    @3
    cG
    cS
    @0
    reldmdprd
    brrelex2i
    adantr
    #
    @24
    vs
    cS
    cvv
    cG
    cvv
    wcel
    @12
    @23
    cG
    @11
    @0
    reldmdprd
    brrelexi
    vg
    cv
    #
    @11
    @0
    wbr
    #
    @29
    @11
    cdprd
    co
    #
    vf
    @14
    @29
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    vh
    @19
    crab
    #
    @29
    @6
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    wceq
    #
    wi
    @24
    vg
    cG
    cvv
    @29
    cG
    wceq
    #
    @30
    @12
    @38
    @23
    @29
    cG
    @11
    @0
    breq1
    @39
    @31
    @13
    @37
    @22
    @29
    cG
    @11
    cdprd
    oveq1
    @39
    @36
    @21
    @39
    vf
    @34
    @35
    @20
    @7
    @39
    @33
    @15
    vh
    @19
    @39
    @32
    c.0
    @14
    cfsupp
    @39
    @32
    cG
    c0g
    cfv
    c.0
    @29
    cG
    c0g
    fveq2
    dprdval.0
    syl6eqr
    breq2d
    rabbidv
    @29
    cG
    @6
    cgsu
    oveq1
    mpteq12dv
    rneqd
    eqeq12d
    imbi12d
    @30
    @29
    cgrp
    wcel
    #
    @11
    @14
    cdm
    #
    @29
    csubg
    cfv
    #
    @14
    wf
    @17
    @14
    cfv
    #
    vy
    cv
    @14
    cfv
    @29
    ccntz
    cfv
    cfv
    wss
    vy
    @41
    @17
    csn
    cdif
    #
    wral
    @43
    @14
    @44
    cima
    cuni
    @42
    cmrc
    cfv
    cfv
    cin
    @32
    csn
    wceq
    wa
    vi
    @41
    wral
    wa
    vh
    cab
    #
    wcel
    #
    wa
    #
    @38
    @30
    @29
    @11
    cop
    #
    @0
    wcel
    @48
    vg
    cgrp
    @29
    csn
    @45
    cxp
    ciun
    #
    wcel
    @47
    @29
    @11
    @0
    df-br
    @0
    @49
    @48
    @49
    cvv
    cdprd
    @37
    cvv
    wcel
    #
    vs
    @45
    wral
    vg
    cgrp
    wral
    @49
    cvv
    cdprd
    wf
    @50
    vg
    vs
    cgrp
    @45
    @36
    @33
    vf
    vh
    @19
    @35
    @18
    cvv
    wcel
    #
    vi
    @16
    wral
    @19
    cvv
    wcel
    @51
    vi
    @16
    @17
    @11
    fvex
    rgenw
    vi
    @16
    @18
    cvv
    ixpexg
    ax-mp
    mptrabex
    rnex
    #
    rgen2w
    vg
    vs
    cgrp
    @45
    @37
    cvv
    cdprd
    vi
    vy
    vf
    vg
    vh
    vs
    df-dprd
    #
    fmpt2x
    mpbi
    fdmi
    eleq2i
    vg
    cgrp
    @45
    @11
    opeliunxp
    3bitri
    @40
    @46
    @50
    @38
    @52
    vg
    vs
    cgrp
    @45
    @37
    cdprd
    cvv
    @53
    ovmpt4g
    mp3an3
    sylbi
    vtoclg
    mpcom
    sbcth
    syl
    @4
    @24
    @26
    vs
    cS
    cvv
    @28
    @4
    @11
    cS
    wceq
    #
    wa
    #
    @12
    @1
    @23
    @10
    @55
    @11
    cS
    cG
    @0
    @4
    @54
    simpr
    #
    breq2d
    @55
    @13
    @5
    @22
    @9
    @55
    @11
    cS
    cG
    cdprd
    @56
    oveq2d
    @55
    @21
    @8
    @55
    vf
    @20
    @7
    cW
    @7
    @55
    @20
    @15
    vh
    vi
    cI
    @17
    cS
    cfv
    #
    cixp
    #
    crab
    cW
    @55
    @15
    vh
    @19
    @58
    @55
    @19
    vi
    cI
    @18
    cixp
    @58
    @55
    vi
    @16
    cI
    @18
    @55
    @16
    @2
    cI
    @55
    @11
    cS
    @56
    dmeqd
    @1
    @3
    @54
    simplr
    eqtrd
    ixpeq1d
    @55
    vi
    cI
    @18
    @57
    @55
    @17
    @11
    cS
    @56
    fveq1d
    ixpeq2dv
    eqtrd
    rabeqdv
    dprdval.w
    syl6eqr
    @55
    @7
    eqidd
    mpteq12dv
    rneqd
    eqeq12d
    imbi12d
    sbcied
    mpbid
    mpd
end
