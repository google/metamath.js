include "cusgr.mm"
include "wcel.mm"
include "cuspgr.mm"
include "cedg.mm"
include "cfv.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "cvtx.mm"
include "wreu.mm"
include "usgruspgr.mm"
include "uspgredg2vtxeu.mm"
include "syl3an1.mm"

theorem usgredg2vtxeu
  let vy: setvar y
  let cE: class E
  let cG: class G
  let cY: class Y
  let vx: setvar x

  disjoint E y
  disjoint G y
  disjoint Y y
  disjoint E x
  disjoint x y
  disjoint G x
  disjoint Y x
  assert |- ( ( G e. USGraph /\ E e. ( Edg ` G ) /\ Y e. E ) -> E! y e. ( Vtx ` G ) E = { Y , y } )

  proof
    cG
    cusgr
    wcel
    cG
    cuspgr
    wcel
    cE
    cG
    cedg
    cfv
    wcel
    cY
    cE
    wcel
    cE
    cY
    vy
    cv
    cpr
    wceq
    vy
    cG
    cvtx
    cfv
    wreu
    cG
    usgruspgr
    vy
    cE
    cG
    cY
    uspgredg2vtxeu
    syl3an1
end
