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
include "elmpt2cl.mm"

theorem natrcl
  let cA: class A
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cN: class N
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
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


  assert |- ( A e. ( F N G ) -> ( F e. ( C Func D ) /\ G e. ( C Func D ) ) )

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
    vs
    vg
    cv
    #
    c1st
    cfv
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
    @3
    @1
    c2nd
    cfv
    co
    cfv
    @6
    vr
    cv
    #
    cfv
    #
    @3
    @7
    cfv
    cop
    @3
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
    @5
    @6
    @3
    @2
    c2nd
    cfv
    co
    cfv
    @6
    @4
    cfv
    @8
    @6
    @9
    cfv
    #
    cop
    @10
    @11
    co
    co
    wceq
    vh
    @6
    @3
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
    @14
    wral
    va
    vx
    @14
    @8
    @12
    cD
    chom
    cfv
    #
    co
    cixp
    crab
    csb
    csb
    cF
    cG
    cN
    cA
    vx
    vy
    @14
    cC
    cD
    @11
    vf
    vg
    vh
    @13
    @15
    cN
    vs
    vr
    va
    natrcl.1
    @14
    eqid
    @13
    eqid
    @15
    eqid
    @11
    eqid
    natfval
    elmpt2cl
end
