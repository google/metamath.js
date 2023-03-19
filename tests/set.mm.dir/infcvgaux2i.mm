include "wcel.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "cv.mm"
include "negeqd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "negex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab2.mm"
include "sylibr.mm"
include "infcvgaux1i.mm"
include "suprubii.mm"
include "syl.mm"
include "wb.mm"
include "eleq1d.mm"
include "vtoclga.mm"
include "suprclii.mm"
include "lenegcon1.mm"
include "sylancl.mm"
include "mpbid.mm"
include "syl5eqbr.mm"

theorem infcvgaux2i
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cX: class X
  let cZ: class Z
  assume infcvg.1: |- R = { x | E. y e. X x = -u A }
  assume infcvg.2: |- ( y e. X -> A e. RR )
  assume infcvg.3: |- Z e. X
  assume infcvg.4: |- E. z e. RR A. w e. R w <_ z
  assume infcvg.5a: |- S = -u sup ( R , RR , < )
  assume infcvg.13: |- ( y = C -> A = B )

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint w z
  disjoint R w
  disjoint R z
  disjoint X x
  disjoint X y
  disjoint Z x
  disjoint Z y
  disjoint C y
  assert |- ( C e. X -> S <_ B )

  proof
    cC
    cX
    wcel
    #
    cS
    cR
    cr
    clt
    csup
    #
    cneg
    #
    cB
    cle
    infcvg.5a
    @0
    cB
    cneg
    #
    @1
    cle
    wbr
    #
    @2
    cB
    cle
    wbr
    #
    @0
    @3
    cR
    wcel
    #
    @4
    @0
    @3
    cA
    cneg
    #
    wceq
    #
    vy
    cX
    wrex
    #
    @6
    @0
    @3
    @3
    wceq
    #
    @9
    @3
    eqid
    @8
    @10
    vy
    cC
    cX
    vy
    cv
    cC
    wceq
    #
    @7
    @3
    @3
    @11
    cA
    cB
    infcvg.13
    negeqd
    eqeq2d
    rspcev
    mpan2
    vx
    cv
    #
    @7
    wceq
    #
    vy
    cX
    wrex
    @9
    vx
    @3
    cR
    cB
    negex
    @12
    @3
    wceq
    @13
    @8
    vy
    cX
    @12
    @3
    @7
    eqeq1
    rexbidv
    infcvg.1
    elab2
    sylibr
    vz
    vw
    cR
    @3
    vx
    vy
    vz
    vw
    cA
    cR
    cX
    cZ
    infcvg.1
    infcvg.2
    infcvg.3
    infcvg.4
    infcvgaux1i
    #
    suprubii
    syl
    @0
    cB
    cr
    wcel
    #
    @1
    cr
    wcel
    @4
    @5
    wb
    cA
    cr
    wcel
    @15
    vy
    cC
    cX
    @11
    cA
    cB
    cr
    infcvg.13
    eleq1d
    infcvg.2
    vtoclga
    vz
    vw
    cR
    @14
    suprclii
    cB
    @1
    lenegcon1
    sylancl
    mpbid
    syl5eqbr
end
