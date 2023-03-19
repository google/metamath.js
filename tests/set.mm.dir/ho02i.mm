include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "ch0o.mm"
include "ralcom.mm"
include "wcel.mm"
include "wb.mm"
include "ffvelrni.mm"
include "c0v.mm"
include "hial02.mm"
include "hial0.mm"
include "bitr4d.mm"
include "syl.mm"
include "ralbiia.mm"
include "ho01i.mm"
include "3bitri.mm"

theorem ho02i
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  assume ho0.1: |- T : ~H --> ~H

  disjoint x y
  disjoint T x
  disjoint T y
  assert |- ( A. x e. ~H A. y e. ~H ( x .ih ( T ` y ) ) = 0 <-> T = 0hop )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cT
    cfv
    #
    csp
    co
    cc0
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    @3
    vx
    chil
    wral
    #
    vy
    chil
    wral
    @2
    @0
    csp
    co
    cc0
    wceq
    vx
    chil
    wral
    #
    vy
    chil
    wral
    cT
    ch0o
    wceq
    @3
    vx
    vy
    chil
    chil
    ralcom
    @4
    @5
    vy
    chil
    @1
    chil
    wcel
    @2
    chil
    wcel
    #
    @4
    @5
    wb
    chil
    chil
    @1
    cT
    ho0.1
    ffvelrni
    @6
    @4
    @2
    c0v
    wceq
    @5
    vx
    @2
    hial02
    vx
    @2
    hial0
    bitr4d
    syl
    ralbiia
    vy
    vx
    cT
    ho0.1
    ho01i
    3bitri
end
