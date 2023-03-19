include "c1stc.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wel.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "wss.mm"
include "is1stc.mm"
include "wex.mm"
include "elin.mm"
include "selpw.mm"
include "anbi2i.mm"
include "bitri.mm"
include "an12.mm"
include "exbii.mm"
include "eluni.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "imbi2i.mm"
include "ralbii.mm"
include "rexbii.mm"

theorem is1stc2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cJ: class J
  let cX: class X
  let vj: setvar j
  assume is1stc.1: |- X = U. J

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint X x
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint X j
  assert |- ( J e. 1stc <-> ( J e. Top /\ A. x e. X E. y e. ~P J ( y ~<_ _om /\ A. z e. J ( x e. z -> E. w e. y ( x e. w /\ w C_ z ) ) ) ) )

  proof
    cJ
    c1stc
    wcel
    cJ
    ctop
    wcel
    #
    vy
    cv
    #
    com
    cdom
    wbr
    #
    vx
    vz
    wel
    #
    vx
    cv
    #
    @1
    vz
    cv
    #
    cpw
    #
    cin
    #
    cuni
    wcel
    #
    wi
    #
    vz
    cJ
    wral
    #
    wa
    #
    vy
    cJ
    cpw
    #
    wrex
    #
    vx
    cX
    wral
    #
    wa
    @0
    @2
    @3
    vx
    vw
    wel
    #
    vw
    cv
    #
    @5
    wss
    #
    wa
    #
    vw
    @1
    wrex
    #
    wi
    #
    vz
    cJ
    wral
    #
    wa
    #
    vy
    @12
    wrex
    #
    vx
    cX
    wral
    #
    wa
    vx
    vy
    vz
    cJ
    cX
    is1stc.1
    is1stc
    @14
    @24
    @0
    @13
    @23
    vx
    cX
    @11
    @22
    vy
    @12
    @10
    @21
    @2
    @9
    @20
    vz
    cJ
    @8
    @19
    @3
    @15
    @16
    @7
    wcel
    #
    wa
    #
    vw
    wex
    vw
    vy
    wel
    #
    @18
    wa
    #
    vw
    wex
    @8
    @19
    @26
    @28
    vw
    @26
    @15
    @27
    @17
    wa
    #
    wa
    @28
    @25
    @29
    @15
    @25
    @27
    @16
    @6
    wcel
    #
    wa
    @29
    @16
    @1
    @6
    elin
    @30
    @17
    @27
    vw
    @5
    selpw
    anbi2i
    bitri
    anbi2i
    @15
    @27
    @17
    an12
    bitri
    exbii
    vw
    @4
    @7
    eluni
    @18
    vw
    @1
    df-rex
    3bitr4i
    imbi2i
    ralbii
    anbi2i
    rexbii
    ralbii
    anbi2i
    bitri
end
