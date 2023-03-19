include "cv.mm"
include "cfv.mm"
include "chom.mm"
include "co.mm"
include "cixp.mm"
include "wcel.mm"
include "wfn.mm"
include "eqid.mm"
include "natixp.mm"
include "ixpfn.mm"
include "syl.mm"

theorem natfn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
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
  let cX: class X
  let c.x: class .x.
  let cY: class Y
  let cJ: class J
  assume natrcl.1: |- N = ( C Nat D )
  assume natixp.2: |- ( ph -> A e. ( <. F , G >. N <. K , L >. ) )
  assume natixp.b: |- B = ( Base ` C )


  assert |- ( ph -> A Fn B )

  proof
    wph
    cA
    vx
    cB
    vx
    cv
    #
    cF
    cfv
    @0
    cK
    cfv
    cD
    chom
    cfv
    #
    co
    #
    cixp
    wcel
    cA
    cB
    wfn
    wph
    vx
    cA
    cB
    cC
    cD
    cF
    cG
    @1
    cK
    cL
    cN
    natrcl.1
    natixp.2
    natixp.b
    @1
    eqid
    natixp
    vx
    cB
    @2
    cA
    ixpfn
    syl
end
