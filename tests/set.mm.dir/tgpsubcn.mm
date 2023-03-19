include "ctgp.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cminusg.mm"
include "cplusg.mm"
include "co.mm"
include "cmpt2.mm"
include "ctx.mm"
include "ccn.mm"
include "eqid.mm"
include "grpsubfval.mm"
include "tgptmd.mm"
include "tgptopon.mm"
include "cnmpt1st.mm"
include "cnmpt2nd.mm"
include "tgpinv.mm"
include "cnmpt21f.mm"
include "cnmpt2plusg.mm"
include "syl5eqel.mm"

theorem tgpsubcn
  let cG: class G
  let cJ: class J
  let c.mi: class .-
  let vx: setvar x
  let vy: setvar y
  assume tgpsubcn.2: |- J = ( TopOpen ` G )
  assume tgpsubcn.3: |- .- = ( -g ` G )


  assert |- ( G e. TopGrp -> .- e. ( ( J tX J ) Cn J ) )

  proof
    cG
    ctgp
    wcel
    #
    c.mi
    vx
    vy
    cG
    cbs
    cfv
    #
    @1
    vx
    cv
    #
    vy
    cv
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    cmpt2
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    vx
    vy
    @1
    @6
    cG
    @4
    c.mi
    @1
    eqid
    #
    @6
    eqid
    #
    @4
    eqid
    #
    tgpsubcn.3
    grpsubfval
    @0
    vx
    vy
    @2
    @5
    @6
    cG
    cJ
    cJ
    cJ
    @1
    @1
    tgpsubcn.2
    @8
    cG
    tgptmd
    cG
    cJ
    @1
    tgpsubcn.2
    @7
    tgptopon
    #
    @10
    @0
    vx
    vy
    cJ
    cJ
    @1
    @1
    @10
    @10
    cnmpt1st
    @0
    vx
    vy
    @3
    @4
    cJ
    cJ
    cJ
    cJ
    @1
    @1
    @10
    @10
    @0
    vx
    vy
    cJ
    cJ
    @1
    @1
    @10
    @10
    cnmpt2nd
    cG
    @4
    cJ
    tgpsubcn.2
    @9
    tgpinv
    cnmpt21f
    cnmpt2plusg
    syl5eqel
end
