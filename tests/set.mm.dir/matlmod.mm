include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cxp.mm"
include "cfrlm.mm"
include "co.mm"
include "clmod.mm"
include "cvv.mm"
include "sqxpexg.mm"
include "eqid.mm"
include "frlmlmod.mm"
include "ancoms.mm"
include "sylan.mm"
include "cbs.mm"
include "cfv.mm"
include "csca.mm"
include "eqidd.mm"
include "matbas.mm"
include "cv.mm"
include "cplusg.mm"
include "matplusg.mm"
include "oveqdr.mm"
include "matsca.mm"
include "cvsca.mm"
include "matvsca.mm"
include "lmodpropd.mm"
include "mpbid.mm"

theorem matlmod
  let cA: class A
  let cR: class R
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume matlmod.a: |- A = ( N Mat R )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> A e. LMod )

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
    cR
    cN
    cN
    cxp
    #
    cfrlm
    co
    #
    clmod
    wcel
    #
    cA
    clmod
    wcel
    @0
    @3
    cvv
    wcel
    #
    @1
    @5
    cN
    cfn
    sqxpexg
    @1
    @6
    @5
    cR
    @4
    @3
    cvv
    @4
    eqid
    #
    frlmlmod
    ancoms
    sylan
    @2
    vx
    vy
    @4
    cbs
    cfv
    #
    @4
    csca
    cfv
    #
    cbs
    cfv
    #
    @9
    @4
    cA
    @2
    @8
    eqidd
    cA
    cR
    @4
    cN
    crg
    matlmod.a
    @7
    matbas
    @2
    vx
    cv
    #
    @8
    wcel
    vy
    cv
    @8
    wcel
    #
    wa
    vx
    vy
    @4
    cplusg
    cfv
    cA
    cplusg
    cfv
    cA
    cR
    @4
    cN
    crg
    matlmod.a
    @7
    matplusg
    oveqdr
    @2
    @9
    eqidd
    cA
    cR
    @4
    cN
    crg
    matlmod.a
    @7
    matsca
    @10
    eqid
    @2
    @11
    @10
    wcel
    @12
    wa
    vx
    vy
    @4
    cvsca
    cfv
    cA
    cvsca
    cfv
    cA
    cR
    @4
    cN
    crg
    matlmod.a
    @7
    matvsca
    oveqdr
    lmodpropd
    mpbid
end
