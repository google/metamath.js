include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cmhm.mm"
include "wceq.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr3.mm"
include "pwspjmhm.mm"
include "syl3anc.mm"
include "simpr1.mm"
include "simpr2.mm"
include "mhmmulg.mm"
include "pwsmnd.mm"
include "adantr.mm"
include "mulgnn0cl.mm"
include "fveq1.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"

theorem pwsmulg
  let cA: class A
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cI: class I
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume pwsmulg.y: |- Y = ( R ^s I )
  assume pwsmulg.b: |- B = ( Base ` Y )
  assume pwsmulg.s: |- .xb = ( .g ` Y )
  assume pwsmulg.t: |- .x. = ( .g ` R )


  assert |- ( ( ( R e. Mnd /\ I e. V ) /\ ( N e. NN0 /\ X e. B /\ A e. I ) ) -> ( ( N .xb X ) ` A ) = ( N .x. ( X ` A ) ) )

  proof
    cR
    cmnd
    wcel
    #
    cI
    cV
    wcel
    #
    wa
    #
    cN
    cn0
    wcel
    #
    cX
    cB
    wcel
    #
    cA
    cI
    wcel
    #
    w3a
    #
    wa
    #
    cN
    cX
    c.xb
    co
    #
    vx
    cB
    cA
    vx
    cv
    #
    cfv
    #
    cmpt
    #
    cfv
    #
    cN
    cX
    @11
    cfv
    #
    c.x
    co
    #
    cA
    @8
    cfv
    #
    cN
    cA
    cX
    cfv
    #
    c.x
    co
    @7
    @11
    cY
    cR
    cmhm
    co
    wcel
    #
    @3
    @4
    @12
    @14
    wceq
    @7
    @0
    @1
    @5
    @17
    @0
    @1
    @6
    simpll
    @0
    @1
    @6
    simplr
    @2
    @3
    @4
    @5
    simpr3
    vx
    cA
    cB
    cR
    cI
    cV
    cY
    pwsmulg.y
    pwsmulg.b
    pwspjmhm
    syl3anc
    @2
    @3
    @4
    @5
    simpr1
    #
    @2
    @3
    @4
    @5
    simpr2
    #
    cB
    c.xb
    c.x
    @11
    cY
    cR
    cN
    cX
    pwsmulg.b
    pwsmulg.s
    pwsmulg.t
    mhmmulg
    syl3anc
    @7
    @8
    cB
    wcel
    #
    @12
    @15
    wceq
    @7
    cY
    cmnd
    wcel
    #
    @3
    @4
    @20
    @2
    @21
    @6
    cR
    cI
    cV
    cY
    pwsmulg.y
    pwsmnd
    adantr
    @18
    @19
    cB
    c.xb
    cY
    cN
    cX
    pwsmulg.b
    pwsmulg.s
    mulgnn0cl
    syl3anc
    vx
    @8
    @10
    @15
    cB
    @11
    cA
    @9
    @8
    fveq1
    @11
    eqid
    #
    cA
    @8
    fvex
    fvmpt
    syl
    @7
    @13
    @16
    cN
    c.x
    @7
    @4
    @13
    @16
    wceq
    @19
    vx
    cX
    @10
    @16
    cB
    @11
    cA
    @9
    cX
    fveq1
    @22
    cA
    cX
    fvex
    fvmpt
    syl
    oveq2d
    3eqtr3d
end
