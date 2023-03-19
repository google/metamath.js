include "ccom.mm"
include "cvv.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cxp.mm"
include "ciun.mm"
include "relco.mm"
include "wrel.mm"
include "reliun.mm"
include "wcel.mm"
include "relxp.mm"
include "a1i.mm"
include "mprgbir.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "vex.mm"
include "opelco2g.mm"
include "mp2an.mm"
include "wrex.mm"
include "eliun.mm"
include "rexv.mm"
include "opelxp.mm"
include "elimasn.mm"
include "opelcnv.mm"
include "bitri.mm"
include "anbi12i.mm"
include "exbii.mm"
include "3bitrri.mm"
include "eqrelriiv.mm"

theorem dfco2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  assert |- ( A o. B ) = U_ x e. _V ( ( `' B " { x } ) X. ( A " { x } ) )

  proof
    vy
    vz
    cA
    cB
    ccom
    #
    vx
    cvv
    cB
    ccnv
    #
    vx
    cv
    #
    csn
    #
    cima
    #
    cA
    @3
    cima
    #
    cxp
    #
    ciun
    #
    cA
    cB
    relco
    @7
    wrel
    @6
    wrel
    #
    vx
    cvv
    vx
    cvv
    @6
    reliun
    @8
    @2
    cvv
    wcel
    @4
    @5
    relxp
    a1i
    mprgbir
    vy
    cv
    #
    vz
    cv
    #
    cop
    #
    @0
    wcel
    #
    @9
    @2
    cop
    cB
    wcel
    #
    @2
    @10
    cop
    cA
    wcel
    #
    wa
    #
    vx
    wex
    #
    @11
    @7
    wcel
    #
    @9
    cvv
    wcel
    @10
    cvv
    wcel
    @12
    @16
    wb
    vy
    vex
    #
    vz
    vex
    #
    vx
    @9
    @10
    cA
    cB
    cvv
    cvv
    opelco2g
    mp2an
    @17
    @11
    @6
    wcel
    #
    vx
    cvv
    wrex
    @20
    vx
    wex
    @16
    vx
    @11
    cvv
    @6
    eliun
    @20
    vx
    rexv
    @20
    @15
    vx
    @20
    @9
    @4
    wcel
    #
    @10
    @5
    wcel
    #
    wa
    @15
    @9
    @10
    @4
    @5
    opelxp
    @21
    @13
    @22
    @14
    @21
    @2
    @9
    cop
    @1
    wcel
    @13
    @1
    @2
    @9
    vx
    vex
    #
    @18
    elimasn
    @2
    @9
    cB
    @23
    @18
    opelcnv
    bitri
    cA
    @2
    @10
    @23
    @19
    elimasn
    anbi12i
    bitri
    exbii
    3bitrri
    bitri
    eqrelriiv
end
