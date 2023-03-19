include "wcel.mm"
include "wral.mm"
include "cmpt.mm"
include "wfn.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "wi.mm"
include "fnmptf.mm"
include "fnbrfvb.mm"
include "ex.mm"
include "syl.mm"

theorem bj-mptval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cX: class X
  let cY: class Y
  assume bj-mptval.nf: |- F/_ x A


  assert |- ( A. x e. A B e. V -> ( X e. A -> ( ( ( x e. A |-> B ) ` X ) = Y <-> X ( x e. A |-> B ) Y ) ) )

  proof
    cB
    cV
    wcel
    vx
    cA
    wral
    vx
    cA
    cB
    cmpt
    #
    cA
    wfn
    #
    cX
    cA
    wcel
    #
    cX
    @0
    cfv
    cY
    wceq
    cX
    cY
    @0
    wbr
    wb
    #
    wi
    vx
    cA
    cB
    cV
    bj-mptval.nf
    fnmptf
    @1
    @2
    @3
    cA
    cX
    cY
    @0
    fnbrfvb
    ex
    syl
end
