include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "cv.mm"
include "cxp.mm"
include "cmpt2.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "eqid.mm"
include "txval.mm"
include "wss.mm"
include "wceq.mm"
include "cres.mm"
include "bastg.mm"
include "resmpt2.mm"
include "syl2an.mm"
include "resss.mm"
include "syl6eqssr.mm"
include "rnss.mm"
include "syl.mm"
include "wf.mm"
include "wral.mm"
include "cuni.mm"
include "wex.mm"
include "eltg3.mm"
include "bi2anan9.mm"
include "eeanv.mm"
include "an4.mm"
include "ciun.mm"
include "uniiun.mm"
include "xpeq12i.mm"
include "xpiundir.mm"
include "xpiundi.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "3eqtri.mm"
include "cvv.mm"
include "ovex.mm"
include "ssel2.mm"
include "anim12i.mm"
include "an4s.mm"
include "txopn.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "tgiun.mm"
include "sylancr.mm"
include "txbasex.mm"
include "tgidm.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "syl5eqel.mm"
include "xpeq12.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "exlimdvv.mm"
include "syl5bir.mm"
include "sylbid.mm"
include "ralrimivv.mm"
include "fmpt2.mm"
include "sylib.mm"
include "frn.mm"
include "sseqtrd.mm"
include "2basgen.mm"
include "syl2anc.mm"
include "fvex.mm"
include "mp2an.mm"
include "syl6eqr.mm"
include "eqtr2d.mm"

theorem txbasval
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( R e. V /\ S e. W ) -> ( ( topGen ` R ) tX ( topGen ` S ) ) = ( R tX S ) )

  proof
    cR
    cV
    wcel
    #
    cS
    cW
    wcel
    #
    wa
    #
    cR
    cS
    ctx
    co
    #
    vu
    vv
    cR
    cS
    vu
    cv
    #
    vv
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    ctg
    cfv
    #
    cR
    ctg
    cfv
    #
    cS
    ctg
    cfv
    #
    ctx
    co
    #
    vu
    vv
    @8
    cR
    cS
    cV
    cW
    @8
    eqid
    #
    txval
    #
    @2
    @9
    vu
    vv
    @10
    @11
    @6
    cmpt2
    #
    crn
    #
    ctg
    cfv
    #
    @12
    @2
    @8
    @16
    wss
    #
    @16
    @9
    wss
    @9
    @17
    wceq
    @2
    @7
    @15
    wss
    @18
    @2
    @7
    @15
    cR
    cS
    cxp
    #
    cres
    #
    @15
    @0
    cR
    @10
    wss
    cS
    @11
    wss
    @20
    @7
    wceq
    @1
    cR
    cV
    bastg
    cS
    cW
    bastg
    vu
    vv
    @10
    @11
    cR
    cS
    @6
    resmpt2
    syl2an
    @15
    @19
    resss
    syl6eqssr
    @7
    @15
    rnss
    syl
    @2
    @16
    @3
    @9
    @2
    @10
    @11
    cxp
    #
    @3
    @15
    wf
    #
    @16
    @3
    wss
    @2
    @6
    @3
    wcel
    #
    vv
    @11
    wral
    vu
    @10
    wral
    @22
    @2
    @23
    vu
    vv
    @10
    @11
    @2
    @4
    @10
    wcel
    #
    @5
    @11
    wcel
    #
    wa
    vm
    cv
    #
    cR
    wss
    #
    @4
    @26
    cuni
    #
    wceq
    #
    wa
    #
    vm
    wex
    #
    vn
    cv
    #
    cS
    wss
    #
    @5
    @32
    cuni
    #
    wceq
    #
    wa
    #
    vn
    wex
    #
    wa
    #
    @23
    @0
    @24
    @31
    @1
    @25
    @37
    vm
    @4
    cR
    cV
    eltg3
    vn
    @5
    cS
    cW
    eltg3
    bi2anan9
    @38
    @30
    @36
    wa
    #
    vn
    wex
    vm
    wex
    @2
    @23
    @30
    @36
    vm
    vn
    eeanv
    @2
    @39
    @23
    vm
    vn
    @39
    @27
    @33
    wa
    #
    @29
    @35
    wa
    #
    wa
    @2
    @23
    @27
    @29
    @33
    @35
    an4
    @2
    @40
    @41
    @23
    @2
    @40
    wa
    #
    @23
    @41
    @28
    @34
    cxp
    #
    @3
    wcel
    @42
    @43
    vx
    @26
    vy
    @32
    vx
    cv
    #
    vy
    cv
    #
    cxp
    #
    ciun
    #
    ciun
    #
    @3
    @43
    vx
    @26
    @44
    ciun
    #
    vy
    @32
    @45
    ciun
    #
    cxp
    vx
    @26
    @44
    @50
    cxp
    #
    ciun
    @48
    @28
    @49
    @34
    @50
    vx
    @26
    uniiun
    vy
    @32
    uniiun
    xpeq12i
    vx
    @26
    @44
    @50
    xpiundir
    vx
    @26
    @51
    @47
    @51
    @47
    wceq
    @44
    @26
    wcel
    #
    vy
    @32
    @45
    @44
    xpiundi
    a1i
    iuneq2i
    3eqtri
    @42
    @48
    @3
    ctg
    cfv
    #
    @3
    @42
    @3
    cvv
    wcel
    #
    @47
    @3
    wcel
    #
    vx
    @26
    wral
    @48
    @53
    wcel
    cR
    cS
    ctx
    ovex
    #
    @42
    @55
    vx
    @26
    @42
    @52
    wa
    #
    @47
    @53
    @3
    @57
    @54
    @46
    @3
    wcel
    #
    vy
    @32
    wral
    @47
    @53
    wcel
    @56
    @57
    @58
    vy
    @32
    @42
    @52
    @45
    @32
    wcel
    #
    @58
    @2
    @40
    @52
    @59
    wa
    #
    @58
    @40
    @60
    wa
    @2
    @44
    cR
    wcel
    #
    @45
    cS
    wcel
    #
    wa
    #
    @58
    @27
    @52
    @33
    @59
    @63
    @27
    @52
    wa
    @61
    @33
    @59
    wa
    @62
    @26
    cR
    @44
    ssel2
    @32
    cS
    @45
    ssel2
    anim12i
    an4s
    @44
    @45
    cR
    cS
    cV
    cW
    txopn
    sylan2
    anassrs
    anassrs
    ralrimiva
    vy
    @32
    @3
    @46
    cvv
    tgiun
    sylancr
    @42
    @53
    @3
    wceq
    #
    @52
    @2
    @64
    @40
    @2
    @9
    ctg
    cfv
    #
    @9
    @53
    @3
    @2
    @8
    cvv
    wcel
    @65
    @9
    wceq
    vu
    vv
    @8
    cR
    cS
    cV
    cW
    @13
    txbasex
    @8
    cvv
    tgidm
    syl
    @2
    @3
    @9
    ctg
    @14
    fveq2d
    @14
    3eqtr4d
    adantr
    #
    adantr
    eleqtrd
    ralrimiva
    vx
    @26
    @3
    @47
    cvv
    tgiun
    sylancr
    @66
    eleqtrd
    syl5eqel
    @41
    @6
    @43
    @3
    @4
    @28
    @5
    @34
    xpeq12
    eleq1d
    syl5ibrcom
    expimpd
    syl5bi
    exlimdvv
    syl5bir
    sylbid
    ralrimivv
    vu
    vv
    @10
    @11
    @6
    @3
    @15
    @15
    eqid
    fmpt2
    sylib
    @21
    @3
    @15
    frn
    syl
    @14
    sseqtrd
    @8
    @16
    2basgen
    syl2anc
    @10
    cvv
    wcel
    @11
    cvv
    wcel
    @12
    @17
    wceq
    cR
    ctg
    fvex
    cS
    ctg
    fvex
    vu
    vv
    @16
    @10
    @11
    cvv
    cvv
    @16
    eqid
    txval
    mp2an
    syl6eqr
    eqtr2d
end
