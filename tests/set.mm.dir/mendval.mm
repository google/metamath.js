include "wcel.mm"
include "cvv.mm"
include "cmend.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "cpr.mm"
include "cun.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "clmhm.mm"
include "co.mm"
include "cof.mm"
include "cmpt2.mm"
include "ccom.mm"
include "csn.mm"
include "cxp.mm"
include "csb.mm"
include "oveq12.mm"
include "anidms.mm"
include "syl6eqr.mm"
include "csbeq1d.mm"
include "ovex.mm"
include "syl6eqelr.mm"
include "wa.mm"
include "simpr.mm"
include "opeq2d.mm"
include "fveq2.mm"
include "ofeq.mm"
include "syl.mm"
include "oveqdr.mm"
include "mpt2eq123dv.mm"
include "eqidd.mm"
include "tpeq123d.mm"
include "adantr.mm"
include "fveq2d.mm"
include "xpeq1d.mm"
include "oveq123d.mm"
include "preq12d.mm"
include "uneq12d.mm"
include "csbied.mm"
include "eqtrd.mm"
include "df-mend.mm"
include "tpex.mm"
include "prex.mm"
include "unex.mm"
include "fvmpt.mm"

theorem mendval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cM: class M
  let cX: class X
  let vb: setvar b
  let vm: setvar m
  assume mendval.b: |- B = ( M LMHom M )
  assume mendval.p: |- .+ = ( x e. B , y e. B |-> ( x oF ( +g ` M ) y ) )
  assume mendval.t: |- .X. = ( x e. B , y e. B |-> ( x o. y ) )
  assume mendval.s: |- S = ( Scalar ` M )
  assume mendval.v: |- .x. = ( x e. ( Base ` S ) , y e. B |-> ( ( ( Base ` M ) X. { x } ) oF ( .s ` M ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint M x
  disjoint M y
  disjoint b m
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint m x
  disjoint m y
  disjoint B m
  disjoint M b
  disjoint M m
  disjoint .+ b
  disjoint .+ m
  disjoint S b
  disjoint S m
  disjoint .X. b
  disjoint .X. m
  disjoint .x. b
  disjoint .x. m
  assert |- ( M e. X -> ( MEndo ` M ) = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. } ) )

  proof
    cM
    cX
    wcel
    cM
    cvv
    wcel
    cM
    cmend
    cfv
    cnx
    cbs
    cfv
    #
    cB
    cop
    #
    cnx
    cplusg
    cfv
    #
    c.pl
    cop
    #
    cnx
    cmulr
    cfv
    #
    c.xp
    cop
    #
    ctp
    #
    cnx
    csca
    cfv
    #
    cS
    cop
    #
    cnx
    cvsca
    cfv
    #
    c.x
    cop
    #
    cpr
    #
    cun
    #
    wceq
    cM
    cX
    elex
    vm
    cM
    vb
    vm
    cv
    #
    @13
    clmhm
    co
    #
    @0
    vb
    cv
    #
    cop
    #
    @2
    vx
    vy
    @15
    @15
    vx
    cv
    #
    vy
    cv
    #
    @13
    cplusg
    cfv
    #
    cof
    #
    co
    #
    cmpt2
    #
    cop
    #
    @4
    vx
    vy
    @15
    @15
    @17
    @18
    ccom
    #
    cmpt2
    #
    cop
    #
    ctp
    #
    @7
    @13
    csca
    cfv
    #
    cop
    #
    @9
    vx
    vy
    @28
    cbs
    cfv
    #
    @15
    @13
    cbs
    cfv
    #
    @17
    csn
    #
    cxp
    #
    @18
    @13
    cvsca
    cfv
    #
    cof
    #
    co
    #
    cmpt2
    #
    cop
    #
    cpr
    #
    cun
    #
    csb
    #
    @12
    cvv
    cmend
    @13
    cM
    wceq
    #
    @41
    vb
    cB
    @40
    csb
    @12
    @42
    vb
    @14
    cB
    @40
    @42
    @14
    cM
    cM
    clmhm
    co
    #
    cB
    @42
    @14
    @43
    wceq
    @13
    cM
    @13
    cM
    clmhm
    oveq12
    anidms
    mendval.b
    syl6eqr
    #
    csbeq1d
    @42
    vb
    cB
    @40
    @12
    cvv
    @42
    cB
    @14
    cvv
    @44
    @13
    @13
    clmhm
    ovex
    syl6eqelr
    @42
    @15
    cB
    wceq
    #
    wa
    #
    @27
    @6
    @39
    @11
    @46
    @16
    @1
    @23
    @3
    @26
    @5
    @46
    @15
    cB
    @0
    @42
    @45
    simpr
    #
    opeq2d
    @46
    @22
    c.pl
    @2
    @46
    @22
    vx
    vy
    cB
    cB
    @17
    @18
    cM
    cplusg
    cfv
    #
    cof
    #
    co
    #
    cmpt2
    c.pl
    @46
    vx
    vy
    @15
    @15
    @21
    cB
    cB
    @50
    @47
    @47
    @42
    @45
    vx
    vy
    @20
    @49
    @42
    @19
    @48
    wceq
    @20
    @49
    wceq
    @13
    cM
    cplusg
    fveq2
    @19
    @48
    ofeq
    syl
    oveqdr
    mpt2eq123dv
    mendval.p
    syl6eqr
    opeq2d
    @46
    @25
    c.xp
    @4
    @46
    @25
    vx
    vy
    cB
    cB
    @24
    cmpt2
    c.xp
    @46
    vx
    vy
    @15
    @15
    @24
    cB
    cB
    @24
    @47
    @47
    @46
    @24
    eqidd
    mpt2eq123dv
    mendval.t
    syl6eqr
    opeq2d
    tpeq123d
    @46
    @29
    @8
    @38
    @10
    @46
    @28
    cS
    @7
    @46
    @28
    cM
    csca
    cfv
    #
    cS
    @42
    @28
    @51
    wceq
    @45
    @13
    cM
    csca
    fveq2
    adantr
    mendval.s
    syl6eqr
    #
    opeq2d
    @46
    @37
    c.x
    @9
    @46
    @37
    vx
    vy
    cS
    cbs
    cfv
    #
    cB
    cM
    cbs
    cfv
    #
    @32
    cxp
    #
    @18
    cM
    cvsca
    cfv
    #
    cof
    #
    co
    #
    cmpt2
    c.x
    @46
    vx
    vy
    @30
    @15
    @36
    @53
    cB
    @58
    @46
    @28
    cS
    cbs
    @52
    fveq2d
    @47
    @46
    @33
    @55
    @18
    @18
    @35
    @57
    @46
    @34
    @56
    wceq
    #
    @35
    @57
    wceq
    @42
    @59
    @45
    @13
    cM
    cvsca
    fveq2
    adantr
    @34
    @56
    ofeq
    syl
    @46
    @31
    @54
    @32
    @42
    @31
    @54
    wceq
    @45
    @13
    cM
    cbs
    fveq2
    adantr
    xpeq1d
    @46
    @18
    eqidd
    oveq123d
    mpt2eq123dv
    mendval.v
    syl6eqr
    opeq2d
    preq12d
    uneq12d
    csbied
    eqtrd
    vx
    vy
    vm
    vb
    df-mend
    @6
    @11
    @1
    @3
    @5
    tpex
    @8
    @10
    prex
    unex
    fvmpt
    syl
end
