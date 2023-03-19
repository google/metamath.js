include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "clt.mm"
include "cinf.mm"
include "crio.mm"
include "lbinf.mm"
include "lbcl.mm"
include "eqeltrd.mm"

theorem lbinfcl
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let vz: setvar z

  disjoint S x
  disjoint S y
  disjoint x y
  disjoint S z
  disjoint x z
  disjoint y z
  assert |- ( ( S C_ RR /\ E. x e. S A. y e. S x <_ y ) -> inf ( S , RR , < ) e. S )

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
    cS
    cr
    clt
    cinf
    @0
    vx
    cS
    crio
    cS
    vx
    vy
    cS
    lbinf
    vx
    vy
    cS
    lbcl
    eqeltrd
end
