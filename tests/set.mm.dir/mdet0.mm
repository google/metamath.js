include "ccrg.mm"
include "wcel.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wex.mm"
include "wa.mm"
include "n0.mm"
include "cmpt2.mm"
include "weq.mm"
include "cif.mm"
include "crg.mm"
include "crngring.mm"
include "anim1i.mm"
include "ancomd.mm"
include "adantr.mm"
include "c0g.mm"
include "mat0op.mm"
include "syl5eq.mm"
include "syl.mm"
include "fveq2d.mm"
include "ifid.mm"
include "eqcomi.mm"
include "a1i.mm"
include "mpt2eq3dv.mm"
include "cbs.mm"
include "eqid.mm"
include "simpll.mm"
include "simpr.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "mndidcl.mm"
include "3ad2ant1.mm"
include "mdetr0.mm"
include "3eqtrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem mdet0
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cN: class N
  let c.0: class .0.
  let cZ: class Z
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  assume mdet0.d: |- D = ( N maDet R )
  assume mdet0.a: |- A = ( N Mat R )
  assume mdet0.b: |- B = ( Base ` A )
  assume mdet0.z: |- Z = ( 0g ` A )
  assume mdet0.0: |- .0. = ( 0g ` R )


  assert |- ( ( R e. CRing /\ N e. Fin /\ N =/= (/) ) -> ( D ` Z ) = .0. )

  proof
    cR
    ccrg
    wcel
    #
    cN
    cfn
    wcel
    #
    cN
    c0
    wne
    #
    cZ
    cD
    cfv
    #
    c.0
    wceq
    #
    @2
    vi
    cv
    #
    cN
    wcel
    #
    vi
    wex
    @0
    @1
    wa
    #
    @4
    vi
    cN
    n0
    @7
    @6
    @4
    vi
    @7
    @6
    @4
    @7
    @6
    wa
    #
    @3
    vx
    vy
    cN
    cN
    c.0
    cmpt2
    #
    cD
    cfv
    vx
    vy
    cN
    cN
    vx
    vi
    weq
    #
    c.0
    c.0
    cif
    #
    cmpt2
    #
    cD
    cfv
    c.0
    @8
    cZ
    @9
    cD
    @8
    @1
    cR
    crg
    wcel
    #
    wa
    #
    cZ
    @9
    wceq
    @7
    @14
    @6
    @7
    @13
    @1
    @0
    @13
    @1
    cR
    crngring
    #
    anim1i
    ancomd
    adantr
    @14
    cZ
    cA
    c0g
    cfv
    @9
    mdet0.z
    cA
    cR
    vx
    vy
    cN
    c.0
    mdet0.a
    mdet0.0
    mat0op
    syl5eq
    syl
    fveq2d
    @8
    @9
    @12
    cD
    @8
    vx
    vy
    cN
    cN
    c.0
    @11
    c.0
    @11
    wceq
    @8
    @11
    c.0
    @10
    c.0
    ifid
    eqcomi
    a1i
    mpt2eq3dv
    fveq2d
    @8
    cD
    cR
    vx
    vy
    @5
    cR
    cbs
    cfv
    #
    cN
    c.0
    c.0
    mdet0.d
    @16
    eqid
    #
    mdet0.0
    @0
    @1
    @6
    simpll
    @7
    @1
    @6
    @0
    @1
    simpr
    adantr
    @8
    vx
    cv
    cN
    wcel
    c.0
    @16
    wcel
    #
    vy
    cv
    cN
    wcel
    @7
    @18
    @6
    @7
    cR
    cmnd
    wcel
    #
    @18
    @0
    @19
    @1
    @0
    @13
    @19
    @15
    cR
    ringmnd
    syl
    adantr
    @16
    cR
    c.0
    @17
    mdet0.0
    mndidcl
    syl
    adantr
    3ad2ant1
    @7
    @6
    simpr
    mdetr0
    3eqtrd
    ex
    exlimdv
    syl5bi
    3impia
end
