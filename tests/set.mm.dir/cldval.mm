include "ctop.mm"
include "wcel.mm"
include "cv.mm"
include "cdif.mm"
include "cpw.mm"
include "crab.mm"
include "cvv.mm"
include "ccld.mm"
include "cfv.mm"
include "wceq.mm"
include "topopn.mm"
include "pwexg.mm"
include "rabexg.mm"
include "3syl.mm"
include "cuni.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "wb.mm"
include "difeq1d.mm"
include "eleq12.mm"
include "mpancom.mm"
include "rabeqbidv.mm"
include "df-cld.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem cldval
  let vx: setvar x
  let cJ: class J
  let cX: class X
  let vy: setvar y
  let vj: setvar j
  assume cldval.1: |- X = U. J

  disjoint J x
  disjoint X x
  disjoint x y
  disjoint j x
  disjoint j y
  disjoint J y
  disjoint J j
  disjoint X j
  assert |- ( J e. Top -> ( Clsd ` J ) = { x e. ~P X | ( X \ x ) e. J } )

  proof
    cJ
    ctop
    wcel
    #
    cX
    vx
    cv
    #
    cdif
    #
    cJ
    wcel
    #
    vx
    cX
    cpw
    #
    crab
    #
    cvv
    wcel
    #
    cJ
    ccld
    cfv
    @5
    wceq
    @0
    cX
    cJ
    wcel
    @4
    cvv
    wcel
    @6
    cJ
    cX
    cldval.1
    topopn
    cX
    cJ
    pwexg
    @3
    vx
    @4
    cvv
    rabexg
    3syl
    vj
    cJ
    vj
    cv
    #
    cuni
    #
    @1
    cdif
    #
    @7
    wcel
    #
    vx
    @8
    cpw
    #
    crab
    @5
    ctop
    cvv
    ccld
    @7
    cJ
    wceq
    #
    @10
    @3
    vx
    @11
    @4
    @12
    @8
    cX
    @12
    @8
    cJ
    cuni
    cX
    @7
    cJ
    unieq
    cldval.1
    syl6eqr
    #
    pweqd
    @9
    @2
    wceq
    @12
    @10
    @3
    wb
    @12
    @8
    cX
    @1
    @13
    difeq1d
    @9
    @2
    @7
    cJ
    eleq12
    mpancom
    rabeqbidv
    vx
    vj
    df-cld
    fvmptg
    mpdan
end
