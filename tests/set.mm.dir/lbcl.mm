include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "wreu.mm"
include "crio.mm"
include "wcel.mm"
include "lbreu.mm"
include "riotacl.mm"
include "syl.mm"

theorem lbcl
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let vw: setvar w
  let cA: class A

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint w x
  disjoint w y
  disjoint S w
  disjoint A w
  disjoint A y
  assert |- ( ( S C_ RR /\ E. x e. S A. y e. S x <_ y ) -> ( iota_ x e. S A. y e. S x <_ y ) e. S )

  proof
    cS
    cr
    wss
    vx
    cv
    vy
    cv
    cle
    wbr
    vy
    cS
    wral
    #
    vx
    cS
    wrex
    wa
    @0
    vx
    cS
    wreu
    @0
    vx
    cS
    crio
    cS
    wcel
    vx
    vy
    cS
    lbreu
    @0
    vx
    cS
    riotacl
    syl
end
