include "cnlm.mm"
include "wcel.mm"
include "co.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cngp.mm"
include "clmod.mm"
include "cnrg.mm"
include "w3a.mm"
include "isnlm.mm"
include "simprbi.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem nmvs
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume isnlm.v: |- V = ( Base ` W )
  assume isnlm.n: |- N = ( norm ` W )
  assume isnlm.s: |- .x. = ( .s ` W )
  assume isnlm.f: |- F = ( Scalar ` W )
  assume isnlm.k: |- K = ( Base ` F )
  assume isnlm.a: |- A = ( norm ` F )


  assert |- ( ( W e. NrmMod /\ X e. K /\ Y e. V ) -> ( N ` ( X .x. Y ) ) = ( ( A ` X ) x. ( N ` Y ) ) )

  proof
    cW
    cnlm
    wcel
    #
    cX
    cK
    wcel
    #
    cY
    cV
    wcel
    #
    cX
    cY
    c.x
    co
    #
    cN
    cfv
    #
    cX
    cA
    cfv
    #
    cY
    cN
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    cN
    cfv
    #
    @9
    cA
    cfv
    #
    @10
    cN
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vy
    cV
    wral
    vx
    cK
    wral
    #
    @1
    @2
    wa
    @8
    @0
    cW
    cngp
    wcel
    cW
    clmod
    wcel
    cF
    cnrg
    wcel
    w3a
    @17
    vx
    vy
    cA
    c.x
    cF
    cK
    cN
    cV
    cW
    isnlm.v
    isnlm.n
    isnlm.s
    isnlm.f
    isnlm.k
    isnlm.a
    isnlm
    simprbi
    @16
    @8
    cX
    @10
    c.x
    co
    #
    cN
    cfv
    #
    @5
    @14
    cmul
    co
    #
    wceq
    vx
    vy
    cX
    cY
    cK
    cV
    @9
    cX
    wceq
    #
    @12
    @19
    @15
    @20
    @21
    @11
    @18
    cN
    @9
    cX
    @10
    c.x
    oveq1
    fveq2d
    @21
    @13
    @5
    @14
    cmul
    @9
    cX
    cA
    fveq2
    oveq1d
    eqeq12d
    @10
    cY
    wceq
    #
    @19
    @4
    @20
    @7
    @22
    @18
    @3
    cN
    @10
    cY
    cX
    c.x
    oveq2
    fveq2d
    @22
    @14
    @6
    @5
    cmul
    @10
    cY
    cN
    fveq2
    oveq2d
    eqeq12d
    rspc2v
    syl5com
    3impib
end
