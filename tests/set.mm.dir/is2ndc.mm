include "c2ndc.mm"
include "wcel.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "ctb.mm"
include "wrex.mm"
include "cab.mm"
include "df-2ndc.mm"
include "eleq2i.mm"
include "cvv.mm"
include "simpr.mm"
include "fvex.mm"
include "syl6eqelr.mm"
include "rexlimivw.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elab3.mm"
include "bitri.mm"

theorem is2ndc
  let vx: setvar x
  let cJ: class J
  let vj: setvar j
  let vy: setvar y
  let cB: class B

  disjoint J x
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint x y
  disjoint J y
  disjoint B x
  assert |- ( J e. 2ndc <-> E. x e. TopBases ( x ~<_ _om /\ ( topGen ` x ) = J ) )

  proof
    cJ
    c2ndc
    wcel
    cJ
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @0
    ctg
    cfv
    #
    vj
    cv
    #
    wceq
    #
    wa
    #
    vx
    ctb
    wrex
    #
    vj
    cab
    #
    wcel
    @1
    @2
    cJ
    wceq
    #
    wa
    #
    vx
    ctb
    wrex
    #
    c2ndc
    @7
    cJ
    vx
    vj
    df-2ndc
    eleq2i
    @6
    @10
    vj
    cJ
    @9
    cJ
    cvv
    wcel
    vx
    ctb
    @9
    cJ
    @2
    cvv
    @1
    @8
    simpr
    @0
    ctg
    fvex
    syl6eqelr
    rexlimivw
    @3
    cJ
    wceq
    #
    @5
    @9
    vx
    ctb
    @11
    @4
    @8
    @1
    @3
    cJ
    @2
    eqeq2
    anbi2d
    rexbidv
    elab3
    bitri
end
