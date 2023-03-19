include "cn0.mm"
include "wcel.mm"
include "ctmd.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "ccn.mm"
include "wi.mm"
include "c0g.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "oveq1.mm"
include "eqid.mm"
include "mulg0.mm"
include "sylan9eq.mm"
include "mpteq2dva.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "mpteq2dv.mm"
include "tmdtopon.mm"
include "cmnd.mm"
include "tmdmnd.mm"
include "mndidcl.mm"
include "syl.mm"
include "cnmptc.mm"
include "wa.mm"
include "cplusg.mm"
include "oveq2.mm"
include "cbvmptv.mm"
include "mulgnn0p1.mm"
include "syl3an1.mm"
include "3expa.mm"
include "adantlr.mm"
include "syl5eq.mm"
include "simpll.mm"
include "ctopon.mm"
include "simpr.mm"
include "syl5eqelr.mm"
include "cnmptid.mm"
include "cnmpt1plusg.mm"
include "eqeltrd.mm"
include "ex.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem tmdmulg
  let vx: setvar x
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cJ: class J
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vy: setvar y
  assume tgpmulg.j: |- J = ( TopOpen ` G )
  assume tgpmulg.t: |- .x. = ( .g ` G )
  assume tgpmulg.b: |- B = ( Base ` G )

  disjoint B x
  disjoint G x
  disjoint J x
  disjoint .x. x
  disjoint N x
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint n x
  disjoint n y
  disjoint B n
  disjoint x y
  disjoint B y
  disjoint G k
  disjoint G n
  disjoint G y
  disjoint J k
  disjoint J n
  disjoint J y
  disjoint .x. k
  disjoint .x. n
  disjoint .x. y
  disjoint N n
  assert |- ( ( G e. TopMnd /\ N e. NN0 ) -> ( x e. B |-> ( N .x. x ) ) e. ( J Cn J ) )

  proof
    cN
    cn0
    wcel
    cG
    ctmd
    wcel
    #
    vx
    cB
    cN
    vx
    cv
    #
    c.x
    co
    #
    cmpt
    #
    cJ
    cJ
    ccn
    co
    #
    wcel
    #
    @0
    vx
    cB
    vn
    cv
    #
    @1
    c.x
    co
    #
    cmpt
    #
    @4
    wcel
    #
    wi
    @0
    vx
    cB
    cG
    c0g
    cfv
    #
    cmpt
    #
    @4
    wcel
    #
    wi
    @0
    vx
    cB
    vk
    cv
    #
    @1
    c.x
    co
    #
    cmpt
    #
    @4
    wcel
    #
    wi
    @0
    vx
    cB
    @13
    c1
    caddc
    co
    #
    @1
    c.x
    co
    #
    cmpt
    #
    @4
    wcel
    #
    wi
    @0
    @5
    wi
    vn
    vk
    cN
    @6
    cc0
    wceq
    #
    @9
    @12
    @0
    @21
    @8
    @11
    @4
    @21
    vx
    cB
    @7
    @10
    @21
    @1
    cB
    wcel
    @7
    cc0
    @1
    c.x
    co
    @10
    @6
    cc0
    @1
    c.x
    oveq1
    cB
    c.x
    cG
    @1
    @10
    tgpmulg.b
    @10
    eqid
    #
    tgpmulg.t
    mulg0
    sylan9eq
    mpteq2dva
    eleq1d
    imbi2d
    @6
    @13
    wceq
    #
    @9
    @16
    @0
    @23
    @8
    @15
    @4
    @23
    vx
    cB
    @7
    @14
    @6
    @13
    @1
    c.x
    oveq1
    mpteq2dv
    eleq1d
    imbi2d
    @6
    @17
    wceq
    #
    @9
    @20
    @0
    @24
    @8
    @19
    @4
    @24
    vx
    cB
    @7
    @18
    @6
    @17
    @1
    c.x
    oveq1
    mpteq2dv
    eleq1d
    imbi2d
    @6
    cN
    wceq
    #
    @9
    @5
    @0
    @25
    @8
    @3
    @4
    @25
    vx
    cB
    @7
    @2
    @6
    cN
    @1
    c.x
    oveq1
    mpteq2dv
    eleq1d
    imbi2d
    @0
    vx
    @10
    cJ
    cJ
    cB
    cB
    cG
    cJ
    cB
    tgpmulg.j
    tgpmulg.b
    tmdtopon
    #
    @26
    @0
    cG
    cmnd
    wcel
    #
    @10
    cB
    wcel
    cG
    tmdmnd
    #
    cB
    cG
    @10
    tgpmulg.b
    @22
    mndidcl
    syl
    cnmptc
    @13
    cn0
    wcel
    #
    @0
    @16
    @20
    @0
    @29
    @16
    @20
    wi
    @0
    @29
    wa
    #
    @16
    @20
    @30
    @16
    wa
    #
    @19
    vy
    cB
    @13
    vy
    cv
    #
    c.x
    co
    #
    @32
    cG
    cplusg
    cfv
    #
    co
    #
    cmpt
    #
    @4
    @31
    @19
    vy
    cB
    @17
    @32
    c.x
    co
    #
    cmpt
    @36
    vx
    vy
    cB
    @18
    @37
    @1
    @32
    @17
    c.x
    oveq2
    cbvmptv
    @31
    vy
    cB
    @37
    @35
    @30
    @32
    cB
    wcel
    #
    @37
    @35
    wceq
    #
    @16
    @0
    @29
    @38
    @39
    @0
    @27
    @29
    @38
    @39
    @28
    cB
    @34
    c.x
    cG
    @13
    @32
    tgpmulg.b
    tgpmulg.t
    @34
    eqid
    #
    mulgnn0p1
    syl3an1
    3expa
    adantlr
    mpteq2dva
    syl5eq
    @31
    vy
    @33
    @32
    @34
    cG
    cJ
    cJ
    cB
    tgpmulg.j
    @40
    @0
    @29
    @16
    simpll
    #
    @31
    @0
    cJ
    cB
    ctopon
    cfv
    wcel
    @41
    @26
    syl
    #
    @31
    vy
    cB
    @33
    cmpt
    @15
    @4
    vx
    vy
    cB
    @14
    @33
    @1
    @32
    @13
    c.x
    oveq2
    cbvmptv
    @30
    @16
    simpr
    syl5eqelr
    @31
    vy
    cJ
    cB
    @42
    cnmptid
    cnmpt1plusg
    eqeltrd
    ex
    expcom
    a2d
    nn0ind
    impcom
end
