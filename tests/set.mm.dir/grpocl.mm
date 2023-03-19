include "cgr.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "co.mm"
include "wfo.mm"
include "grpofo.mm"
include "fof.mm"
include "syl.mm"
include "fovrn.mm"
include "syl3an1.mm"

theorem grpocl
  let cA: class A
  let cB: class B
  let cG: class G
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let vu: setvar u
  let cU: class U
  assume grpfo.1: |- X = ran G


  assert |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( A G B ) e. X )

  proof
    cG
    cgr
    wcel
    #
    cX
    cX
    cxp
    #
    cX
    cG
    wf
    #
    cA
    cX
    wcel
    cB
    cX
    wcel
    cA
    cB
    cG
    co
    cX
    wcel
    @0
    @1
    cX
    cG
    wfo
    @2
    cG
    cX
    grpfo.1
    grpofo
    @1
    cX
    cG
    fof
    syl
    cA
    cB
    cX
    cX
    cX
    cG
    fovrn
    syl3an1
end
