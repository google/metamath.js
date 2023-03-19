include "ccvs.mm"
include "wcel.mm"
include "cclm.mm"
include "clvec.mm"
include "wa.mm"
include "cabl.mm"
include "cc.mm"
include "wss.mm"
include "cxp.mm"
include "wf.mm"
include "c1.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "caddc.mm"
include "cmul.mm"
include "w3a.mm"
include "cin.mm"
include "df-cvs.mm"
include "eleq2i.mm"
include "elin.mm"
include "bitri.mm"
include "clmod.mm"
include "lveclmod.mm"
include "lmodabl.mm"
include "syl.mm"
include "adantl.mm"
include "csca.mm"
include "cfv.mm"
include "eqid.mm"
include "clmsscn.mm"
include "clmlmod.mm"
include "lmodscaf.mm"
include "jca.mm"
include "adantr.mm"
include "cur.mm"
include "clm1.mm"
include "oveq1d.mm"
include "anim1i.mm"
include "lmodvs1.mm"
include "eqtrd.mm"
include "simplr.mm"
include "simpllr.mm"
include "simpr.mm"
include "3jca.mm"
include "lmodvsdi.mm"
include "ralrimiva.mm"
include "cplusg.mm"
include "clmadd.mm"
include "oveqd.mm"
include "lmodvsdir.mm"
include "cmulr.mm"
include "clmmul.mm"
include "lmodvsass.mm"
include "sylbi.mm"

theorem cvsi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cW: class W
  let cX: class X
  assume cvsi.x: |- X = ( Base ` W )
  assume cvsi.a: |- .+ = ( +g ` W )
  assume cvsi.s: |- S = ( Base ` ( Scalar ` W ) )
  assume cvsi.m: |- .xb = ( .sf ` W )
  assume cvsi.t: |- .x. = ( .s ` W )

  disjoint W x
  disjoint W y
  disjoint W z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X y
  disjoint X z
  disjoint S z
  assert |- ( W e. CVec -> ( W e. Abel /\ ( S C_ CC /\ .xb : ( S X. X ) --> X ) /\ A. x e. X ( ( 1 .x. x ) = x /\ A. y e. S ( A. z e. X ( y .x. ( x .+ z ) ) = ( ( y .x. x ) .+ ( y .x. z ) ) /\ A. z e. S ( ( ( y + z ) .x. x ) = ( ( y .x. x ) .+ ( z .x. x ) ) /\ ( ( y x. z ) .x. x ) = ( y .x. ( z .x. x ) ) ) ) ) ) )

  proof
    cW
    ccvs
    wcel
    #
    cW
    cclm
    wcel
    #
    cW
    clvec
    wcel
    #
    wa
    #
    cW
    cabl
    wcel
    #
    cS
    cc
    wss
    #
    cS
    cX
    cxp
    cX
    c.xb
    wf
    #
    wa
    #
    c1
    vx
    cv
    #
    c.x
    co
    #
    @8
    wceq
    #
    vy
    cv
    #
    @8
    vz
    cv
    #
    c.pl
    co
    c.x
    co
    @11
    @8
    c.x
    co
    #
    @11
    @12
    c.x
    co
    c.pl
    co
    wceq
    #
    vz
    cX
    wral
    #
    @11
    @12
    caddc
    co
    #
    @8
    c.x
    co
    #
    @13
    @12
    @8
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    @11
    @12
    cmul
    co
    #
    @8
    c.x
    co
    #
    @11
    @18
    c.x
    co
    #
    wceq
    #
    wa
    #
    vz
    cS
    wral
    #
    wa
    #
    vy
    cS
    wral
    #
    wa
    #
    vx
    cX
    wral
    #
    w3a
    @0
    cW
    cclm
    clvec
    cin
    #
    wcel
    @3
    ccvs
    @31
    cW
    df-cvs
    eleq2i
    cW
    cclm
    clvec
    elin
    bitri
    @3
    @4
    @7
    @30
    @2
    @4
    @1
    @2
    cW
    clmod
    wcel
    #
    @4
    cW
    lveclmod
    cW
    lmodabl
    syl
    adantl
    @1
    @7
    @2
    @1
    @5
    @6
    cW
    csca
    cfv
    #
    cS
    cW
    @33
    eqid
    #
    cvsi.s
    clmsscn
    @1
    @32
    @6
    cW
    clmlmod
    #
    cX
    c.xb
    @33
    cS
    cW
    cvsi.x
    @34
    cvsi.s
    cvsi.m
    lmodscaf
    syl
    jca
    adantr
    @1
    @30
    @2
    @1
    @29
    vx
    cX
    @1
    @8
    cX
    wcel
    #
    wa
    #
    @10
    @28
    @37
    @9
    @33
    cur
    cfv
    #
    @8
    c.x
    co
    #
    @8
    @37
    c1
    @38
    @8
    c.x
    @1
    c1
    @38
    wceq
    @36
    @33
    cW
    @34
    clm1
    adantr
    oveq1d
    @37
    @32
    @36
    wa
    @39
    @8
    wceq
    @1
    @32
    @36
    @35
    anim1i
    c.x
    @38
    @33
    cX
    cW
    @8
    cvsi.x
    @34
    cvsi.t
    @38
    eqid
    lmodvs1
    syl
    eqtrd
    @37
    @27
    vy
    cS
    @37
    @11
    cS
    wcel
    #
    wa
    #
    @15
    @26
    @41
    @14
    vz
    cX
    @41
    @12
    cX
    wcel
    #
    wa
    #
    @32
    @40
    @36
    @42
    w3a
    #
    wa
    @14
    @43
    @32
    @44
    @41
    @32
    @42
    @37
    @32
    @40
    @1
    @32
    @36
    @35
    adantr
    adantr
    #
    adantr
    @43
    @40
    @36
    @42
    @37
    @40
    @42
    simplr
    @1
    @36
    @40
    @42
    simpllr
    @41
    @42
    simpr
    3jca
    jca
    c.pl
    @11
    c.x
    @33
    cS
    cX
    cW
    @8
    @12
    cvsi.x
    cvsi.a
    @34
    cvsi.t
    cvsi.s
    lmodvsdi
    syl
    ralrimiva
    @41
    @25
    vz
    cS
    @41
    @12
    cS
    wcel
    #
    wa
    #
    @20
    @24
    @47
    @17
    @11
    @12
    @33
    cplusg
    cfv
    #
    co
    #
    @8
    c.x
    co
    #
    @19
    @47
    @16
    @49
    @8
    c.x
    @47
    caddc
    @48
    @11
    @12
    @41
    caddc
    @48
    wceq
    #
    @46
    @37
    @51
    @40
    @1
    @51
    @36
    @33
    cW
    @34
    clmadd
    adantr
    adantr
    adantr
    oveqd
    oveq1d
    @47
    @32
    @40
    @46
    @36
    w3a
    #
    wa
    #
    @50
    @19
    wceq
    @47
    @32
    @52
    @41
    @32
    @46
    @45
    adantr
    @47
    @40
    @46
    @36
    @41
    @40
    @46
    @37
    @40
    simpr
    adantr
    @41
    @46
    simpr
    @41
    @36
    @46
    @37
    @36
    @40
    @1
    @36
    simpr
    adantr
    adantr
    3jca
    jca
    #
    c.pl
    @48
    @11
    @12
    c.x
    @33
    cS
    cX
    cW
    @8
    cvsi.x
    cvsi.a
    @34
    cvsi.t
    cvsi.s
    @48
    eqid
    lmodvsdir
    syl
    eqtrd
    @47
    @22
    @11
    @12
    @33
    cmulr
    cfv
    #
    co
    #
    @8
    c.x
    co
    #
    @23
    @47
    @21
    @56
    @8
    c.x
    @47
    cmul
    @55
    @11
    @12
    @41
    cmul
    @55
    wceq
    #
    @46
    @37
    @58
    @40
    @1
    @58
    @36
    @33
    cW
    @34
    clmmul
    adantr
    adantr
    adantr
    oveqd
    oveq1d
    @47
    @53
    @57
    @23
    wceq
    @54
    @11
    @12
    c.x
    @55
    @33
    cS
    cX
    cW
    @8
    cvsi.x
    @34
    cvsi.t
    cvsi.s
    @55
    eqid
    lmodvsass
    syl
    eqtrd
    jca
    ralrimiva
    jca
    ralrimiva
    jca
    ralrimiva
    adantr
    3jca
    sylbi
end
