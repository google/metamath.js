include "csn.mm"
include "cres.mm"
include "cima.mm"
include "cxp.mm"
include "relres.mm"
include "relxp.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "ancom.mm"
include "vex.mm"
include "elimasn.mm"
include "elsni.mm"
include "sneqd.mm"
include "imaeq2d.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "opelres.mm"
include "opelxp.mm"
include "3bitr4i.mm"
include "eqrelriiv.mm"

theorem ressn
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( A |` { B } ) = ( { B } X. ( A " { B } ) )

  proof
    vx
    vy
    cA
    cB
    csn
    #
    cres
    #
    @0
    cA
    @0
    cima
    #
    cxp
    #
    cA
    @0
    relres
    @0
    @2
    relxp
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cA
    wcel
    #
    @4
    @0
    wcel
    #
    wa
    #
    @8
    @5
    @2
    wcel
    #
    wa
    #
    @6
    @1
    wcel
    @6
    @3
    wcel
    @9
    @8
    @7
    wa
    @11
    @7
    @8
    ancom
    @8
    @7
    @10
    @7
    @5
    cA
    @4
    csn
    #
    cima
    #
    wcel
    @8
    @10
    cA
    @4
    @5
    vx
    vex
    vy
    vex
    #
    elimasn
    @8
    @13
    @2
    @5
    @8
    @12
    @0
    cA
    @8
    @4
    cB
    @4
    cB
    elsni
    sneqd
    imaeq2d
    eleq2d
    syl5bbr
    pm5.32i
    bitri
    @4
    @5
    cA
    @0
    @14
    opelres
    @4
    @5
    @0
    @2
    opelxp
    3bitr4i
    eqrelriiv
end
