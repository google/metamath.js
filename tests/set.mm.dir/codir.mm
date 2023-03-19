include "cv.mm"
include "cop.mm"
include "cxp.mm"
include "wcel.mm"
include "ccnv.mm"
include "ccom.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wbr.mm"
include "wex.mm"
include "wss.mm"
include "wral.mm"
include "opelxp.mm"
include "df-br.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "brcodir.mm"
include "mp2an.mm"
include "bitr3i.mm"
include "imbi12i.mm"
include "2albii.mm"
include "wrel.mm"
include "relxp.mm"
include "ssrel.mm"
include "ax-mp.mm"
include "r2al.mm"
include "3bitr4i.mm"

theorem codir
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint V z
  disjoint W z
  assert |- ( ( A X. B ) C_ ( `' R o. R ) <-> A. x e. A A. y e. B E. z ( x R z /\ y R z ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cA
    cB
    cxp
    #
    wcel
    #
    @2
    cR
    ccnv
    cR
    ccom
    #
    wcel
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    @0
    cA
    wcel
    @1
    cB
    wcel
    wa
    #
    @0
    vz
    cv
    #
    cR
    wbr
    @1
    @10
    cR
    wbr
    wa
    vz
    wex
    #
    wi
    #
    vy
    wal
    vx
    wal
    @3
    @5
    wss
    #
    @11
    vy
    cB
    wral
    vx
    cA
    wral
    @7
    @12
    vx
    vy
    @4
    @9
    @6
    @11
    @0
    @1
    cA
    cB
    opelxp
    @6
    @0
    @1
    @5
    wbr
    #
    @11
    @0
    @1
    @5
    df-br
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    @14
    @11
    wb
    vx
    vex
    vy
    vex
    vz
    @0
    @1
    cR
    cvv
    cvv
    brcodir
    mp2an
    bitr3i
    imbi12i
    2albii
    @3
    wrel
    @13
    @8
    wb
    cA
    cB
    relxp
    vx
    vy
    @3
    @5
    ssrel
    ax-mp
    @11
    vx
    vy
    cA
    cB
    r2al
    3bitr4i
end
