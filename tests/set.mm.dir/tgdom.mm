include "wcel.mm"
include "cpw.mm"
include "cvv.mm"
include "ctg.mm"
include "cfv.mm"
include "cdom.mm"
include "wbr.mm"
include "pwexg.mm"
include "cv.mm"
include "cin.mm"
include "wss.mm"
include "inss1.mm"
include "vpwex.mm"
include "inex2.mm"
include "elpw.mm"
include "mpbir.mm"
include "a1i.mm"
include "wa.mm"
include "wceq.mm"
include "cuni.mm"
include "unieq.mm"
include "adantl.mm"
include "eltg4i.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "pweq.mm"
include "ineq2d.mm"
include "impbid1.mm"
include "dom2.mm"
include "syl.mm"

theorem tgdom
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cC: class C


  assert |- ( B e. V -> ( topGen ` B ) ~<_ ~P B )

  proof
    cB
    cV
    wcel
    cB
    cpw
    #
    cvv
    wcel
    cB
    ctg
    cfv
    #
    @0
    cdom
    wbr
    cB
    cV
    pwexg
    vx
    vy
    @1
    @0
    cB
    vx
    cv
    #
    cpw
    #
    cin
    #
    cB
    vy
    cv
    #
    cpw
    #
    cin
    #
    cvv
    @4
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    @8
    @4
    cB
    wss
    cB
    @3
    inss1
    @4
    cB
    @3
    cB
    vx
    vpwex
    inex2
    elpw
    mpbir
    a1i
    @9
    @5
    @1
    wcel
    #
    wa
    #
    @4
    @7
    wceq
    #
    @2
    @5
    wceq
    #
    @11
    @12
    @13
    @11
    @12
    wa
    @4
    cuni
    #
    @7
    cuni
    #
    @2
    @5
    @12
    @14
    @15
    wceq
    @11
    @4
    @7
    unieq
    adantl
    @9
    @2
    @14
    wceq
    @10
    @12
    @2
    cB
    eltg4i
    ad2antrr
    @10
    @5
    @15
    wceq
    @9
    @12
    @5
    cB
    eltg4i
    ad2antlr
    3eqtr4d
    ex
    @13
    @3
    @6
    cB
    @2
    @5
    pweq
    ineq2d
    impbid1
    dom2
    syl
end
