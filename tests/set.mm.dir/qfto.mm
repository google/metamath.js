include "cv.mm"
include "cop.mm"
include "cxp.mm"
include "wcel.mm"
include "ccnv.mm"
include "cun.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wbr.mm"
include "wo.mm"
include "wss.mm"
include "wral.mm"
include "opelxp.mm"
include "brun.mm"
include "df-br.mm"
include "vex.mm"
include "brcnv.mm"
include "orbi2i.mm"
include "3bitr3i.mm"
include "imbi12i.mm"
include "2albii.mm"
include "wrel.mm"
include "wb.mm"
include "relxp.mm"
include "ssrel.mm"
include "ax-mp.mm"
include "r2al.mm"
include "3bitr4i.mm"

theorem qfto
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vz: setvar z
  let cS: class S
  let cV: class V
  let cW: class W

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint V z
  disjoint W z
  assert |- ( ( A X. B ) C_ ( R u. `' R ) <-> A. x e. A A. y e. B ( x R y \/ y R x ) )

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
    cR
    ccnv
    #
    cun
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
    @1
    cR
    wbr
    #
    @1
    @0
    cR
    wbr
    #
    wo
    #
    wi
    #
    vy
    wal
    vx
    wal
    @3
    @6
    wss
    #
    @13
    vy
    cB
    wral
    vx
    cA
    wral
    @8
    @14
    vx
    vy
    @4
    @10
    @7
    @13
    @0
    @1
    cA
    cB
    opelxp
    @0
    @1
    @6
    wbr
    @11
    @0
    @1
    @5
    wbr
    #
    wo
    @7
    @13
    @0
    @1
    cR
    @5
    brun
    @0
    @1
    @6
    df-br
    @16
    @12
    @11
    @0
    @1
    cR
    vx
    vex
    vy
    vex
    brcnv
    orbi2i
    3bitr3i
    imbi12i
    2albii
    @3
    wrel
    @15
    @9
    wb
    cA
    cB
    relxp
    vx
    vy
    @3
    @6
    ssrel
    ax-mp
    @13
    vx
    vy
    cA
    cB
    r2al
    3bitr4i
end
