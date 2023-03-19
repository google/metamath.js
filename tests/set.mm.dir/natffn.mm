include "cfunc.mm"
include "co.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cco.mm"
include "wceq.mm"
include "chom.mm"
include "wral.mm"
include "cbs.mm"
include "cixp.mm"
include "crab.mm"
include "csb.mm"
include "eqid.mm"
include "natfval.mm"
include "cvv.mm"
include "wcel.mm"
include "ovex.mm"
include "rgenw.mm"
include "ixpexg.mm"
include "ax-mp.mm"
include "rabex.mm"
include "csbex.mm"
include "fnmpt2i.mm"

theorem natffn
  let cC: class C
  let cD: class D
  let cN: class N
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let cG: class G
  let cH: class H
  let cR: class R
  let va: setvar a
  let vg: setvar g
  let vh: setvar h
  let vr: setvar r
  let vs: setvar s
  let cK: class K
  let wph: wff ph
  let cX: class X
  let cL: class L
  let c.x: class .x.
  let cY: class Y
  let cB: class B
  let cJ: class J
  assume natrcl.1: |- N = ( C Nat D )


  assert |- N Fn ( ( C Func D ) X. ( C Func D ) )

  proof
    vf
    vg
    cC
    cD
    cfunc
    co
    #
    @0
    vr
    vf
    cv
    #
    c1st
    cfv
    #
    vs
    vg
    cv
    #
    c1st
    cfv
    #
    vy
    cv
    #
    va
    cv
    #
    cfv
    vh
    cv
    #
    vx
    cv
    #
    @5
    @1
    c2nd
    cfv
    co
    cfv
    @8
    vr
    cv
    #
    cfv
    #
    @5
    @9
    cfv
    cop
    @5
    vs
    cv
    #
    cfv
    #
    cD
    cco
    cfv
    #
    co
    co
    @7
    @8
    @5
    @3
    c2nd
    cfv
    co
    cfv
    @8
    @6
    cfv
    @10
    @8
    @11
    cfv
    #
    cop
    @12
    @13
    co
    co
    wceq
    vh
    @8
    @5
    cC
    chom
    cfv
    #
    co
    wral
    vy
    cC
    cbs
    cfv
    #
    wral
    vx
    @16
    wral
    #
    va
    vx
    @16
    @10
    @14
    cD
    chom
    cfv
    #
    co
    #
    cixp
    #
    crab
    #
    csb
    #
    csb
    cN
    vx
    vy
    @16
    cC
    cD
    @13
    vf
    vg
    vh
    @15
    @18
    cN
    vs
    vr
    va
    natrcl.1
    @16
    eqid
    @15
    eqid
    @18
    eqid
    @13
    eqid
    natfval
    vr
    @2
    @22
    vs
    @4
    @21
    @17
    va
    @20
    @19
    cvv
    wcel
    #
    vx
    @16
    wral
    @20
    cvv
    wcel
    @23
    vx
    @16
    @10
    @14
    @18
    ovex
    rgenw
    vx
    @16
    @19
    cvv
    ixpexg
    ax-mp
    rabex
    csbex
    csbex
    fnmpt2i
end
