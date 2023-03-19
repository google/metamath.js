include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cixp.mm"
include "wcel.mm"
include "natixp.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fvixp.mm"
include "syl2anc.mm"

theorem natcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let cN: class N
  let cX: class X
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
  let c.x: class .x.
  let cY: class Y
  assume natrcl.1: |- N = ( C Nat D )
  assume natixp.2: |- ( ph -> A e. ( <. F , G >. N <. K , L >. ) )
  assume natixp.b: |- B = ( Base ` C )
  assume natixp.j: |- J = ( Hom ` D )
  assume natcl.1: |- ( ph -> X e. B )


  assert |- ( ph -> ( A ` X ) e. ( ( F ` X ) J ( K ` X ) ) )

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
    #
    @0
    cK
    cfv
    #
    cJ
    co
    #
    cixp
    wcel
    cX
    cB
    wcel
    cX
    cA
    cfv
    cX
    cF
    cfv
    #
    cX
    cK
    cfv
    #
    cJ
    co
    #
    wcel
    wph
    vx
    cA
    cB
    cC
    cD
    cF
    cG
    cJ
    cK
    cL
    cN
    natrcl.1
    natixp.2
    natixp.b
    natixp.j
    natixp
    natcl.1
    vx
    cB
    @3
    cX
    @6
    cA
    @0
    cX
    wceq
    @1
    @4
    @2
    @5
    cJ
    @0
    cX
    cF
    fveq2
    @0
    cX
    cK
    fveq2
    oveq12d
    fvixp
    syl2anc
end
