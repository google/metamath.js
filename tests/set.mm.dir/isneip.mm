include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "wrex.mm"
include "wb.mm"
include "snssi.mm"
include "isnei.mm"
include "sylan2.mm"
include "snssg.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "anbi2d.mm"
include "adantl.mm"
include "bitr4d.mm"

theorem isneip
  let cP: class P
  let vg: setvar g
  let cJ: class J
  let cN: class N
  let cX: class X
  let vj: setvar j
  let vv: setvar v
  let vx: setvar x
  let cS: class S
  assume neifval.1: |- X = U. J

  disjoint J g
  disjoint N g
  disjoint P g
  disjoint X g
  disjoint g j
  disjoint g v
  disjoint g x
  disjoint j v
  disjoint j x
  disjoint J j
  disjoint v x
  disjoint J v
  disjoint J x
  disjoint N v
  disjoint S g
  disjoint S v
  disjoint S x
  disjoint X j
  disjoint X v
  disjoint X x
  assert |- ( ( J e. Top /\ P e. X ) -> ( N e. ( ( nei ` J ) ` { P } ) <-> ( N C_ X /\ E. g e. J ( P e. g /\ g C_ N ) ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    cN
    cP
    csn
    #
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    cN
    cX
    wss
    #
    @2
    vg
    cv
    #
    wss
    #
    @5
    cN
    wss
    #
    wa
    #
    vg
    cJ
    wrex
    #
    wa
    #
    @4
    cP
    @5
    wcel
    #
    @7
    wa
    #
    vg
    cJ
    wrex
    #
    wa
    #
    @1
    @0
    @2
    cX
    wss
    @3
    @10
    wb
    cP
    cX
    snssi
    @2
    vg
    cJ
    cN
    cX
    neifval.1
    isnei
    sylan2
    @1
    @14
    @10
    wb
    @0
    @1
    @13
    @9
    @4
    @1
    @12
    @8
    vg
    cJ
    @1
    @11
    @6
    @7
    cP
    @5
    cX
    snssg
    anbi1d
    rexbidv
    anbi2d
    adantl
    bitr4d
end
