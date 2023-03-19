include "wcel.mm"
include "cvv.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cts.mm"
include "cordt.mm"
include "cpr.mm"
include "cple.mm"
include "coc.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "crab.mm"
include "cuni.mm"
include "cmpt.mm"
include "cun.mm"
include "elex.mm"
include "cipo.mm"
include "wss.mm"
include "wa.mm"
include "copab.mm"
include "csb.mm"
include "cxp.mm"
include "vex.mm"
include "xpex.mm"
include "simpl.mm"
include "prss.mm"
include "sylibr.mm"
include "ssopab2i.mm"
include "df-xp.mm"
include "sseqtr4i.mm"
include "ssexi.mm"
include "a1i.mm"
include "sseq2.mm"
include "anbi1d.mm"
include "opabbidv.mm"
include "syl6eqr.mm"
include "opeq2d.mm"
include "simpr.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "id.mm"
include "rabeq.mm"
include "unieqd.mm"
include "mpteq12dv.mm"
include "adantr.mm"
include "uneq12d.mm"
include "csbied2.mm"
include "df-ipo.mm"
include "prex.mm"
include "unex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem ipoval
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cI: class I
  let c.le: class .<_
  let cV: class V
  let vf: setvar f
  let vo: setvar o
  let cX: class X
  let cY: class Y
  assume ipoval.i: |- I = ( toInc ` F )
  assume ipoval.l: |- .<_ = { <. x , y >. | ( { x , y } C_ F /\ x C_ y ) }

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint I x
  disjoint I y
  disjoint V x
  disjoint V y
  disjoint f o
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint o x
  disjoint o y
  disjoint F o
  disjoint .<_ f
  disjoint .<_ o
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( F e. V -> I = ( { <. ( Base ` ndx ) , F >. , <. ( TopSet ` ndx ) , ( ordTop ` .<_ ) >. } u. { <. ( le ` ndx ) , .<_ >. , <. ( oc ` ndx ) , ( x e. F |-> U. { y e. F | ( y i^i x ) = (/) } ) >. } ) )

  proof
    cF
    cV
    wcel
    cF
    cvv
    wcel
    #
    cI
    cnx
    cbs
    cfv
    #
    cF
    cop
    #
    cnx
    cts
    cfv
    #
    c.le
    cordt
    cfv
    #
    cop
    #
    cpr
    #
    cnx
    cple
    cfv
    #
    c.le
    cop
    #
    cnx
    coc
    cfv
    #
    vx
    cF
    vy
    cv
    #
    vx
    cv
    #
    cin
    c0
    wceq
    #
    vy
    cF
    crab
    #
    cuni
    #
    cmpt
    #
    cop
    #
    cpr
    #
    cun
    #
    wceq
    cF
    cV
    elex
    @0
    cI
    cF
    cipo
    cfv
    @18
    ipoval.i
    vf
    cF
    vo
    @11
    @10
    cpr
    #
    vf
    cv
    #
    wss
    #
    @11
    @10
    wss
    #
    wa
    #
    vx
    vy
    copab
    #
    @1
    @20
    cop
    #
    @3
    vo
    cv
    #
    cordt
    cfv
    #
    cop
    #
    cpr
    #
    @7
    @26
    cop
    #
    @9
    vx
    @20
    @12
    vy
    @20
    crab
    #
    cuni
    #
    cmpt
    #
    cop
    #
    cpr
    #
    cun
    #
    csb
    @18
    cvv
    cipo
    @20
    cF
    wceq
    #
    vo
    @24
    c.le
    @36
    @18
    cvv
    @24
    cvv
    wcel
    @37
    @24
    @20
    @20
    cxp
    #
    @20
    @20
    vf
    vex
    #
    @39
    xpex
    @24
    @11
    @20
    wcel
    @10
    @20
    wcel
    wa
    #
    vx
    vy
    copab
    @38
    @23
    @40
    vx
    vy
    @23
    @21
    @40
    @21
    @22
    simpl
    @11
    @10
    @20
    vx
    vex
    vy
    vex
    prss
    sylibr
    ssopab2i
    vx
    vy
    @20
    @20
    df-xp
    sseqtr4i
    ssexi
    a1i
    @37
    @24
    @19
    cF
    wss
    #
    @22
    wa
    #
    vx
    vy
    copab
    c.le
    @37
    @23
    @42
    vx
    vy
    @37
    @21
    @41
    @22
    @20
    cF
    @19
    sseq2
    anbi1d
    opabbidv
    ipoval.l
    syl6eqr
    @37
    @26
    c.le
    wceq
    #
    wa
    #
    @29
    @6
    @35
    @17
    @44
    @25
    @2
    @28
    @5
    @44
    @20
    cF
    @1
    @37
    @43
    simpl
    opeq2d
    @44
    @27
    @4
    @3
    @44
    @26
    c.le
    cordt
    @37
    @43
    simpr
    #
    fveq2d
    opeq2d
    preq12d
    @44
    @30
    @8
    @34
    @16
    @44
    @26
    c.le
    @7
    @45
    opeq2d
    @44
    @33
    @15
    @9
    @37
    @33
    @15
    wceq
    @43
    @37
    vx
    @20
    @32
    cF
    @14
    @37
    id
    @37
    @31
    @13
    @12
    vy
    @20
    cF
    rabeq
    unieqd
    mpteq12dv
    adantr
    opeq2d
    preq12d
    uneq12d
    csbied2
    vx
    vy
    vf
    vo
    df-ipo
    @6
    @17
    @2
    @5
    prex
    @8
    @16
    prex
    unex
    fvmpt
    syl5eq
    syl
end
