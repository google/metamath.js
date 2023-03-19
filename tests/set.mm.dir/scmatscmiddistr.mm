include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "co.mm"
include "weq.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt2.mm"
include "cdmat.mm"
include "wceq.mm"
include "simprl.mm"
include "cur.mm"
include "cbs.mm"
include "eqid.mm"
include "dmatid.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "jca.mm"
include "dmatscmcl.mm"
include "syldan.mm"
include "simprr.mm"
include "oveqi.mm"
include "dmatmul.mm"
include "syl5eq.mm"
include "w3a.mm"
include "simpll.mm"
include "simplr.mm"
include "3jca.mm"
include "3ad2ant1.mm"
include "3simpc.mm"
include "scmatscmide.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "ifeq1d.mm"
include "mpt2eq3dva.mm"
include "iftrue.mm"
include "adantl.mm"
include "ifeq1da.mm"
include "wral.mm"
include "cvv.mm"
include "eqidd.mm"
include "eqeq12.mm"
include "eqcomi.mm"
include "a1i.mm"
include "ifbieq1d.mm"
include "ovex.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ifex.mm"
include "ovmpt2d.mm"
include "ringcl.mm"
include "syl.mm"
include "sylan.mm"
include "eqtr4d.mm"
include "ralrimivva.mm"
include "wb.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "matbas2d.mm"
include "matring.mm"
include "ringidcl.mm"
include "matvscl.mm"
include "eqmat.mm"
include "mpbird.mm"
include "eqtrd.mm"

theorem scmatscmiddistr
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let c.1: class .1.
  let c.as: class .*
  let cN: class N
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  assume scmatscmide.a: |- A = ( N Mat R )
  assume scmatscmide.b: |- B = ( Base ` R )
  assume scmatscmide.0: |- .0. = ( 0g ` R )
  assume scmatscmide.1: |- .1. = ( 1r ` A )
  assume scmatscmide.m: |- .* = ( .s ` A )
  assume scmatscmiddistr.t: |- .x. = ( .r ` R )
  assume scmatscmiddistr.m: |- .X. = ( .r ` A )


  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( S e. B /\ T e. B ) ) -> ( ( S .* .1. ) .X. ( T .* .1. ) ) = ( ( S .x. T ) .* .1. ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cS
    cB
    wcel
    #
    cT
    cB
    wcel
    #
    wa
    #
    wa
    #
    cS
    c.1
    c.as
    co
    #
    cT
    c.1
    c.as
    co
    #
    c.xp
    co
    #
    vi
    vj
    cN
    cN
    vi
    vj
    weq
    #
    vi
    cv
    #
    vj
    cv
    #
    @7
    co
    #
    @11
    @12
    @8
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    c.0
    cif
    #
    cmpt2
    #
    cS
    cT
    c.x
    co
    #
    c.1
    c.as
    co
    #
    @2
    @5
    @7
    cN
    cR
    cdmat
    co
    #
    wcel
    #
    @8
    @21
    wcel
    #
    wa
    #
    @9
    @18
    wceq
    @6
    @22
    @23
    @2
    @5
    @3
    c.1
    @21
    wcel
    #
    wa
    @22
    @6
    @3
    @25
    @2
    @3
    @4
    simprl
    #
    @2
    @25
    @5
    @2
    c.1
    cA
    cur
    cfv
    @21
    scmatscmide.1
    cA
    cA
    cbs
    cfv
    #
    @21
    cR
    cN
    c.0
    scmatscmide.a
    @27
    eqid
    #
    scmatscmide.0
    @21
    eqid
    #
    dmatid
    syl5eqel
    adantr
    #
    jca
    cA
    @27
    cS
    @21
    cR
    c.as
    cB
    c.1
    cN
    scmatscmide.b
    scmatscmide.a
    @28
    scmatscmide.m
    @29
    dmatscmcl
    syldan
    @2
    @5
    @4
    @25
    wa
    @23
    @6
    @4
    @25
    @2
    @3
    @4
    simprr
    #
    @30
    jca
    cA
    @27
    cT
    @21
    cR
    c.as
    cB
    c.1
    cN
    scmatscmide.b
    scmatscmide.a
    @28
    scmatscmide.m
    @29
    dmatscmcl
    syldan
    jca
    @2
    @24
    wa
    @9
    @7
    @8
    cA
    cmulr
    cfv
    #
    co
    @18
    c.xp
    @32
    @7
    @8
    scmatscmiddistr.m
    oveqi
    vi
    vj
    cA
    @27
    @21
    cR
    cN
    @7
    @8
    c.0
    scmatscmide.a
    @28
    scmatscmide.0
    @29
    dmatmul
    syl5eq
    syldan
    @6
    @18
    vi
    vj
    cN
    cN
    @10
    @10
    cS
    c.0
    cif
    #
    @10
    cT
    c.0
    cif
    #
    @15
    co
    #
    c.0
    cif
    #
    cmpt2
    #
    @20
    @6
    vi
    vj
    cN
    cN
    @17
    @36
    @6
    @11
    cN
    wcel
    #
    @12
    cN
    wcel
    #
    w3a
    #
    @10
    @16
    @35
    c.0
    @40
    @13
    @33
    @14
    @34
    @15
    @40
    @0
    @1
    @3
    w3a
    #
    @38
    @39
    wa
    #
    @13
    @33
    wceq
    @6
    @38
    @41
    @39
    @6
    @0
    @1
    @3
    @0
    @1
    @5
    simpll
    #
    @0
    @1
    @5
    simplr
    #
    @26
    3jca
    3ad2ant1
    @6
    @38
    @39
    3simpc
    #
    cA
    cB
    cS
    cR
    c.1
    @11
    c.as
    @12
    cN
    c.0
    scmatscmide.a
    scmatscmide.b
    scmatscmide.0
    scmatscmide.1
    scmatscmide.m
    scmatscmide
    syl2anc
    @40
    @0
    @1
    @4
    w3a
    #
    @42
    @14
    @34
    wceq
    @6
    @38
    @46
    @39
    @6
    @0
    @1
    @4
    @43
    @44
    @31
    3jca
    3ad2ant1
    @45
    cA
    cB
    cT
    cR
    c.1
    @11
    c.as
    @12
    cN
    c.0
    scmatscmide.a
    scmatscmide.b
    scmatscmide.0
    scmatscmide.1
    scmatscmide.m
    scmatscmide
    syl2anc
    oveq12d
    ifeq1d
    mpt2eq3dva
    @6
    @37
    vi
    vj
    cN
    cN
    @10
    cS
    cT
    @15
    co
    #
    c.0
    cif
    #
    cmpt2
    #
    @20
    @6
    vi
    vj
    cN
    cN
    @36
    @48
    @40
    @10
    @35
    @47
    c.0
    @10
    @35
    @47
    wceq
    @40
    @10
    @33
    cS
    @34
    cT
    @15
    @10
    cS
    c.0
    iftrue
    @10
    cT
    c.0
    iftrue
    oveq12d
    adantl
    ifeq1da
    mpt2eq3dva
    @6
    @49
    @20
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    @49
    co
    #
    @51
    @52
    @20
    co
    #
    wceq
    #
    vy
    cN
    wral
    vx
    cN
    wral
    #
    @6
    @55
    vx
    vy
    cN
    cN
    @6
    @51
    cN
    wcel
    #
    @52
    cN
    wcel
    #
    wa
    #
    wa
    #
    @53
    vx
    vy
    weq
    #
    @19
    c.0
    cif
    #
    @54
    @60
    vi
    vj
    @51
    @52
    cN
    cN
    @48
    @62
    @49
    cvv
    @60
    @49
    eqidd
    vi
    vx
    weq
    vj
    vy
    weq
    wa
    #
    @48
    @62
    wceq
    @60
    @63
    @10
    @61
    @47
    @19
    c.0
    @11
    @51
    @12
    @52
    eqeq12
    @47
    @19
    wceq
    @63
    @15
    c.x
    cS
    cT
    c.x
    @15
    scmatscmiddistr.t
    eqcomi
    oveqi
    a1i
    ifbieq1d
    adantl
    @6
    @57
    @58
    simprl
    @6
    @57
    @58
    simprr
    @62
    cvv
    wcel
    @60
    @61
    @19
    c.0
    cS
    cT
    c.x
    ovex
    c.0
    cR
    c0g
    cfv
    cvv
    scmatscmide.0
    cR
    c0g
    fvex
    eqeltri
    ifex
    a1i
    ovmpt2d
    @6
    @0
    @1
    @19
    cB
    wcel
    #
    w3a
    @59
    @54
    @62
    wceq
    @6
    @0
    @1
    @64
    @43
    @44
    @6
    @1
    @3
    @4
    w3a
    #
    @64
    @6
    @1
    @3
    @4
    @44
    @26
    @31
    3jca
    #
    cB
    cR
    c.x
    cS
    cT
    scmatscmide.b
    scmatscmiddistr.t
    ringcl
    syl
    #
    3jca
    cA
    cB
    @19
    cR
    c.1
    @51
    c.as
    @52
    cN
    c.0
    scmatscmide.a
    scmatscmide.b
    scmatscmide.0
    scmatscmide.1
    scmatscmide.m
    scmatscmide
    sylan
    eqtr4d
    ralrimivva
    @6
    @49
    @27
    wcel
    @20
    @27
    wcel
    #
    @50
    @56
    wb
    @6
    vi
    vj
    cA
    @27
    @48
    cR
    cB
    cN
    crg
    scmatscmide.a
    scmatscmide.b
    @28
    @43
    @44
    @6
    @38
    @48
    cB
    wcel
    @39
    @6
    @10
    @47
    c.0
    cB
    @6
    @65
    @47
    cB
    wcel
    @66
    cB
    cR
    @15
    cS
    cT
    scmatscmide.b
    @15
    eqid
    ringcl
    syl
    @2
    c.0
    cB
    wcel
    #
    @5
    @1
    @69
    @0
    cB
    cR
    c.0
    scmatscmide.b
    scmatscmide.0
    ring0cl
    adantl
    adantr
    ifcld
    3ad2ant1
    matbas2d
    @2
    @5
    @64
    c.1
    @27
    wcel
    #
    wa
    @68
    @6
    @64
    @70
    @67
    @2
    @70
    @5
    @2
    cA
    crg
    wcel
    @70
    cA
    cR
    cN
    scmatscmide.a
    matring
    @27
    cA
    c.1
    @28
    scmatscmide.1
    ringidcl
    syl
    adantr
    jca
    cA
    @27
    @19
    cR
    c.as
    cB
    cN
    c.1
    scmatscmide.b
    scmatscmide.a
    @28
    scmatscmide.m
    matvscl
    syldan
    cA
    @27
    cR
    vx
    vy
    cN
    @49
    @20
    scmatscmide.a
    @28
    eqmat
    syl2anc
    mpbird
    eqtrd
    eqtrd
    eqtrd
end
