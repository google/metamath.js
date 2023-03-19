include "cgr.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "co.mm"
include "grpodivf.mm"
include "fovrn.mm"
include "syl3an1.mm"

theorem grpodivcl
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume grpdivf.1: |- X = ran G
  assume grpdivf.3: |- D = ( /g ` G )


  assert |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( A D B ) e. X )

  proof
    cG
    cgr
    wcel
    cX
    cX
    cxp
    cX
    cD
    wf
    cA
    cX
    wcel
    cB
    cX
    wcel
    cA
    cB
    cD
    co
    cX
    wcel
    cD
    cG
    cX
    grpdivf.1
    grpdivf.3
    grpodivf
    cA
    cB
    cX
    cX
    cX
    cD
    fovrn
    syl3an1
end
