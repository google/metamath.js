include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "mat2pmatval.mm"
include "adantr.mm"
include "oveq12.mm"
include "fveq2d.mm"
include "adantl.mm"
include "simprl.mm"
include "simprr.mm"
include "fvexd.mm"
include "ovmpt2d.mm"

theorem mat2pmatvalel
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume mat2pmatfval.t: |- T = ( N matToPolyMat R )
  assume mat2pmatfval.a: |- A = ( N Mat R )
  assume mat2pmatfval.b: |- B = ( Base ` A )
  assume mat2pmatfval.p: |- P = ( Poly1 ` R )
  assume mat2pmatfval.s: |- S = ( algSc ` P )


  assert |- ( ( ( N e. Fin /\ R e. V /\ M e. B ) /\ ( X e. N /\ Y e. N ) ) -> ( X ( T ` M ) Y ) = ( S ` ( X M Y ) ) )

  proof
    cN
    cfn
    wcel
    cR
    cV
    wcel
    cM
    cB
    wcel
    w3a
    #
    cX
    cN
    wcel
    #
    cY
    cN
    wcel
    #
    wa
    #
    wa
    #
    vx
    vy
    cX
    cY
    cN
    cN
    vx
    cv
    #
    vy
    cv
    #
    cM
    co
    #
    cS
    cfv
    #
    cX
    cY
    cM
    co
    #
    cS
    cfv
    #
    cM
    cT
    cfv
    #
    cvv
    @0
    @11
    vx
    vy
    cN
    cN
    @8
    cmpt2
    wceq
    @3
    vx
    vy
    cA
    cB
    cP
    cR
    cS
    cT
    cM
    cN
    cV
    mat2pmatfval.t
    mat2pmatfval.a
    mat2pmatfval.b
    mat2pmatfval.p
    mat2pmatfval.s
    mat2pmatval
    adantr
    @5
    cX
    wceq
    @6
    cY
    wceq
    wa
    #
    @8
    @10
    wceq
    @4
    @12
    @7
    @9
    cS
    @5
    cX
    @6
    cY
    cM
    oveq12
    fveq2d
    adantl
    @0
    @1
    @2
    simprl
    @0
    @1
    @2
    simprr
    @4
    @9
    cS
    fvexd
    ovmpt2d
end
