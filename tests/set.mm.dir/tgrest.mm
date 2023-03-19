include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ctg.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "wex.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "eltg3.mm"
include "ax-mp.mm"
include "cin.mm"
include "cmpt.mm"
include "cima.mm"
include "wfun.mm"
include "simpll.mm"
include "funmpt.mm"
include "a1i.mm"
include "crn.mm"
include "restval.mm"
include "sseq2d.mm"
include "biimpa.mm"
include "wral.mm"
include "wfn.mm"
include "vex.mm"
include "inex1.mm"
include "rgenw.mm"
include "eqid.mm"
include "fnmpt.mm"
include "fnima.mm"
include "mp2b.mm"
include "syl6sseqr.mm"
include "ssimaexg.mm"
include "syl3anc.mm"
include "wi.mm"
include "ciun.mm"
include "cres.mm"
include "df-ima.mm"
include "resmpt.mm"
include "adantl.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "unieqd.mm"
include "dfiun3.mm"
include "syl6eqr.mm"
include "iunin1.mm"
include "syl6eq.mm"
include "fvex.mm"
include "simpr.mm"
include "adantr.mm"
include "uniiun.mm"
include "eltg3i.mm"
include "syl5eqelr.mm"
include "adantlr.mm"
include "elrestr.mm"
include "eqeltrd.mm"
include "unieq.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "mpd.mm"
include "eleq1.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "sylancr.mm"
include "wf.mm"
include "ineq1i.mm"
include "eqtr4i.mm"
include "simplll.mm"
include "simpllr.mm"
include "sselda.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "syl5eqel.mm"
include "ineq1.mm"
include "sylbid.mm"
include "imp.mm"
include "eqsstrd.mm"
include "eqssd.mm"

theorem tgrest
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cX: class X


  assert |- ( ( B e. V /\ A e. W ) -> ( topGen ` ( B |`t A ) ) = ( ( topGen ` B ) |`t A ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cW
    wcel
    #
    wa
    #
    cB
    cA
    crest
    co
    #
    ctg
    cfv
    #
    cB
    ctg
    cfv
    #
    cA
    crest
    co
    #
    @2
    vx
    @4
    @6
    vx
    cv
    #
    @4
    wcel
    #
    vy
    cv
    #
    @3
    wss
    #
    @7
    @9
    cuni
    #
    wceq
    #
    wa
    #
    vy
    wex
    #
    @2
    @7
    @6
    wcel
    #
    @3
    cvv
    wcel
    #
    @8
    @14
    wb
    cB
    cA
    crest
    ovex
    #
    vy
    @7
    @3
    cvv
    eltg3
    ax-mp
    @2
    @13
    @15
    vy
    @2
    @10
    @12
    @15
    @2
    @10
    wa
    #
    @15
    @12
    @11
    @6
    wcel
    #
    @18
    vz
    cv
    #
    cB
    wss
    #
    @9
    vx
    cB
    @7
    cA
    cin
    #
    cmpt
    #
    @20
    cima
    #
    wceq
    #
    wa
    #
    vz
    wex
    #
    @19
    @18
    @0
    @23
    wfun
    #
    @9
    @23
    cB
    cima
    #
    wss
    @27
    @0
    @1
    @10
    simpll
    @28
    @18
    vx
    cB
    @22
    funmpt
    a1i
    @18
    @9
    @23
    crn
    #
    @29
    @2
    @10
    @9
    @30
    wss
    @2
    @3
    @30
    @9
    vx
    cA
    cB
    cV
    cW
    restval
    sseq2d
    biimpa
    @22
    cvv
    wcel
    #
    vx
    cB
    wral
    @23
    cB
    wfn
    @29
    @30
    wceq
    @31
    vx
    cB
    @7
    cA
    vx
    vex
    inex1
    #
    rgenw
    vx
    cB
    @22
    @23
    cvv
    @23
    eqid
    fnmpt
    cB
    @23
    fnima
    mp2b
    syl6sseqr
    vz
    cB
    @9
    cV
    @23
    ssimaexg
    syl3anc
    @2
    @27
    @19
    wi
    @10
    @2
    @26
    @19
    vz
    @2
    @21
    @25
    @19
    @2
    @21
    wa
    #
    @19
    @25
    @24
    cuni
    #
    @6
    wcel
    @33
    @34
    vx
    @20
    @7
    ciun
    #
    cA
    cin
    #
    @6
    @33
    @34
    vx
    @20
    @22
    ciun
    #
    @36
    @33
    @34
    vx
    @20
    @22
    cmpt
    #
    crn
    #
    cuni
    #
    @37
    @33
    @24
    @39
    @33
    @24
    @23
    @20
    cres
    #
    crn
    @39
    @23
    @20
    df-ima
    @33
    @41
    @38
    @21
    @41
    @38
    wceq
    @2
    vx
    cB
    @20
    @22
    resmpt
    adantl
    rneqd
    syl5eq
    unieqd
    vx
    @20
    @22
    @32
    dfiun3
    #
    syl6eqr
    vx
    @20
    cA
    @7
    iunin1
    #
    syl6eq
    @33
    @5
    cvv
    wcel
    #
    @1
    @35
    @5
    wcel
    #
    @36
    @6
    wcel
    @44
    @33
    cB
    ctg
    fvex
    #
    a1i
    @2
    @1
    @21
    @0
    @1
    simpr
    #
    adantr
    @0
    @21
    @45
    @1
    @0
    @21
    wa
    @35
    @20
    cuni
    #
    @5
    vx
    @20
    uniiun
    #
    @20
    cB
    cV
    eltg3i
    syl5eqelr
    adantlr
    @35
    cA
    @5
    cvv
    cW
    elrestr
    syl3anc
    eqeltrd
    @25
    @11
    @34
    @6
    @9
    @24
    unieq
    eleq1d
    syl5ibrcom
    expimpd
    exlimdv
    adantr
    mpd
    @7
    @11
    @6
    eleq1
    syl5ibrcom
    expimpd
    exlimdv
    syl5bi
    ssrdv
    @2
    @6
    vw
    @5
    vw
    cv
    #
    cA
    cin
    #
    cmpt
    #
    crn
    #
    @4
    @2
    @44
    @1
    @6
    @53
    wceq
    @46
    @47
    vw
    cA
    @5
    cvv
    cW
    restval
    sylancr
    @2
    @5
    @4
    @52
    wf
    @53
    @4
    wss
    @2
    vw
    @5
    @51
    @4
    @52
    @2
    @50
    @5
    wcel
    #
    @51
    @4
    wcel
    #
    @2
    @54
    @21
    @50
    @48
    wceq
    #
    wa
    #
    vz
    wex
    #
    @55
    @0
    @54
    @58
    wb
    @1
    vz
    @50
    cB
    cV
    eltg3
    adantr
    @2
    @57
    @55
    vz
    @2
    @21
    @56
    @55
    @33
    @55
    @56
    @48
    cA
    cin
    #
    @4
    wcel
    @33
    @59
    @37
    @4
    @59
    @36
    @37
    @48
    @35
    cA
    @49
    ineq1i
    @43
    eqtr4i
    @33
    @37
    @40
    @4
    @42
    @33
    @16
    @39
    @3
    wss
    #
    @40
    @4
    wcel
    @17
    @33
    @20
    @3
    @38
    wf
    @60
    @33
    vx
    @20
    @22
    @3
    @38
    @33
    @7
    @20
    wcel
    #
    wa
    @0
    @1
    @7
    cB
    wcel
    @22
    @3
    wcel
    @0
    @1
    @21
    @61
    simplll
    @0
    @1
    @21
    @61
    simpllr
    @33
    @20
    cB
    @7
    @2
    @21
    simpr
    sselda
    @7
    cA
    cB
    cV
    cW
    elrestr
    syl3anc
    @38
    eqid
    fmptd
    @20
    @3
    @38
    frn
    syl
    @39
    @3
    cvv
    eltg3i
    sylancr
    syl5eqel
    syl5eqel
    @56
    @51
    @59
    @4
    @50
    @48
    cA
    ineq1
    eleq1d
    syl5ibrcom
    expimpd
    exlimdv
    sylbid
    imp
    @52
    eqid
    fmptd
    @5
    @4
    @52
    frn
    syl
    eqsstrd
    eqssd
end
