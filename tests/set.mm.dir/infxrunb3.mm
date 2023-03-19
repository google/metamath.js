include "cxr.mm"
include "wss.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "cle.mm"
include "cinf.mm"
include "cmnf.mm"
include "wceq.mm"
include "unb2ltle.mm"
include "infxrunb2.mm"
include "bitr3d.mm"

theorem infxrunb3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A w
  disjoint w x
  disjoint w y
  assert |- ( A C_ RR* -> ( A. x e. RR E. y e. A y <_ x <-> inf ( A , RR* , < ) = -oo ) )

  proof
    cA
    cxr
    wss
    vy
    cv
    #
    vw
    cv
    clt
    wbr
    vy
    cA
    wrex
    vw
    cr
    wral
    @0
    vx
    cv
    cle
    wbr
    vy
    cA
    wrex
    vx
    cr
    wral
    cA
    cxr
    clt
    cinf
    cmnf
    wceq
    vx
    vy
    vw
    cA
    unb2ltle
    vw
    vy
    cA
    infxrunb2
    bitr3d
end
