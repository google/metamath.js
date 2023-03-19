include "cr.mm"
include "wcel.mm"
include "cnr.mm"
include "c0r.mm"
include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "df-r.mm"
include "eleq2i.mm"
include "elxp2.mm"
include "0r.mm"
include "elexi.mm"
include "opeq2.mm"
include "eqeq2d.mm"
include "rexsn.mm"
include "eqcom.mm"
include "bitri.mm"
include "rexbii.mm"

theorem elreal
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. RR <-> E. x e. R. <. x , 0R >. = A )

  proof
    cA
    cr
    wcel
    cA
    cnr
    c0r
    csn
    #
    cxp
    #
    wcel
    #
    vx
    cv
    #
    c0r
    cop
    #
    cA
    wceq
    #
    vx
    cnr
    wrex
    #
    cr
    @1
    cA
    df-r
    eleq2i
    @2
    cA
    @3
    vy
    cv
    #
    cop
    #
    wceq
    #
    vy
    @0
    wrex
    #
    vx
    cnr
    wrex
    @6
    vx
    vy
    cA
    cnr
    @0
    elxp2
    @10
    @5
    vx
    cnr
    @10
    cA
    @4
    wceq
    #
    @5
    @9
    @11
    vy
    c0r
    c0r
    cnr
    0r
    elexi
    @7
    c0r
    wceq
    @8
    @4
    cA
    @7
    c0r
    @3
    opeq2
    eqeq2d
    rexsn
    cA
    @4
    eqcom
    bitri
    rexbii
    bitri
    bitri
end
