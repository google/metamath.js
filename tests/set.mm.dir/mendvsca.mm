include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "co.mm"
include "wceq.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "id.mm"
include "oveqan12d.mm"
include "cvsca.mm"
include "cfv.mm"
include "cmpt2.mm"
include "mendvscafval.mm"
include "eqtri.mm"
include "ovex.mm"
include "ovmpt2a.mm"

theorem mendvsca
  let cA: class A
  let cB: class B
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cE: class E
  let cK: class K
  let cM: class M
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume mendvscafval.a: |- A = ( MEndo ` M )
  assume mendvscafval.v: |- .x. = ( .s ` M )
  assume mendvscafval.b: |- B = ( Base ` A )
  assume mendvscafval.s: |- S = ( Scalar ` M )
  assume mendvscafval.k: |- K = ( Base ` S )
  assume mendvscafval.e: |- E = ( Base ` M )
  assume mendvsca.w: |- .xb = ( .s ` A )


  assert |- ( ( X e. K /\ Y e. B ) -> ( X .xb Y ) = ( ( E X. { X } ) oF .x. Y ) )

  proof
    vx
    vy
    cX
    cY
    cK
    cB
    cE
    vx
    cv
    #
    csn
    #
    cxp
    #
    vy
    cv
    #
    c.x
    cof
    #
    co
    #
    cE
    cX
    csn
    #
    cxp
    #
    cY
    @4
    co
    c.xb
    @0
    cX
    wceq
    #
    @3
    cY
    wceq
    #
    @2
    @7
    @3
    cY
    @4
    @8
    @1
    @6
    cE
    @0
    cX
    sneq
    xpeq2d
    @9
    id
    oveqan12d
    c.xb
    cA
    cvsca
    cfv
    vx
    vy
    cK
    cB
    @5
    cmpt2
    mendvsca.w
    vx
    vy
    cA
    cB
    cS
    c.x
    cE
    cK
    cM
    mendvscafval.a
    mendvscafval.v
    mendvscafval.b
    mendvscafval.s
    mendvscafval.k
    mendvscafval.e
    mendvscafval
    eqtri
    @7
    cY
    @4
    ovex
    ovmpt2a
end
