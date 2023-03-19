include "cnv.mm"
include "wcel.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "caddc.mm"
include "cmul.mm"
include "cop.mm"
include "cabs.mm"
include "cif.mm"
include "cns.mm"
include "cfv.mm"
include "cims.mm"
include "cmopn.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "c1.mm"
include "cv.mm"
include "cnmcv.mm"
include "cdiv.mm"
include "cba.mm"
include "eqid.mm"
include "elimnvu.mm"
include "smcnlem.mm"
include "dedth.mm"

theorem smcn
  let cC: class C
  let cS: class S
  let cU: class U
  let cJ: class J
  let cK: class K
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T
  let cX: class X
  assume smcn.c: |- C = ( IndMet ` U )
  assume smcn.j: |- J = ( MetOpen ` C )
  assume smcn.s: |- S = ( .sOLD ` U )
  assume smcn.k: |- K = ( TopOpen ` CCfld )


  assert |- ( U e. NrmCVec -> S e. ( ( K tX J ) Cn J ) )

  proof
    cU
    cnv
    wcel
    #
    cS
    cK
    cJ
    ctx
    co
    #
    cJ
    ccn
    co
    #
    wcel
    @0
    cU
    caddc
    cmul
    cop
    cabs
    cop
    #
    cif
    #
    cns
    cfv
    #
    cK
    @4
    cims
    cfv
    #
    cmopn
    cfv
    #
    ctx
    co
    #
    @7
    ccn
    co
    #
    wcel
    cU
    @3
    cU
    @4
    wceq
    #
    cS
    @5
    @2
    @9
    @10
    cS
    cU
    cns
    cfv
    @5
    smcn.s
    cU
    @4
    cns
    fveq2
    syl5eq
    @10
    @1
    @8
    cJ
    @7
    ccn
    @10
    cJ
    @7
    cK
    ctx
    @10
    cJ
    cC
    cmopn
    cfv
    @7
    smcn.j
    @10
    cC
    @6
    cmopn
    @10
    cC
    cU
    cims
    cfv
    @6
    smcn.c
    cU
    @4
    cims
    fveq2
    syl5eq
    fveq2d
    syl5eq
    #
    oveq2d
    @11
    oveq12d
    eleq12d
    vx
    vy
    @6
    @5
    c1
    c1
    vy
    cv
    @4
    cnmcv
    cfv
    #
    cfv
    vx
    cv
    cabs
    cfv
    caddc
    co
    c1
    caddc
    co
    vr
    cv
    cdiv
    co
    caddc
    co
    cdiv
    co
    #
    @4
    @7
    cK
    @12
    @4
    cba
    cfv
    #
    vr
    @6
    eqid
    @7
    eqid
    @5
    eqid
    smcn.k
    @14
    eqid
    @12
    eqid
    cU
    elimnvu
    @13
    eqid
    smcnlem
    dedth
end
