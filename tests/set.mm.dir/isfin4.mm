include "cv.mm"
include "wpss.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wn.mm"
include "cfin4.mm"
include "wceq.mm"
include "psseq2.mm"
include "breq2.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "notbid.mm"
include "df-fin4.mm"
include "elab2g.mm"

theorem isfin4
  let vy: setvar y
  let cA: class A
  let cV: class V
  let vx: setvar x
  let cB: class B
  let cX: class X

  disjoint A y
  disjoint x y
  disjoint A x
  disjoint B y
  disjoint X x
  assert |- ( A e. V -> ( A e. Fin4 <-> -. E. y ( y C. A /\ y ~~ A ) ) )

  proof
    vy
    cv
    #
    vx
    cv
    #
    wpss
    #
    @0
    @1
    cen
    wbr
    #
    wa
    #
    vy
    wex
    #
    wn
    @0
    cA
    wpss
    #
    @0
    cA
    cen
    wbr
    #
    wa
    #
    vy
    wex
    #
    wn
    vx
    cA
    cfin4
    cV
    @1
    cA
    wceq
    #
    @5
    @9
    @10
    @4
    @8
    vy
    @10
    @2
    @6
    @3
    @7
    @1
    cA
    @0
    psseq2
    @1
    cA
    @0
    cen
    breq2
    anbi12d
    exbidv
    notbid
    vx
    vy
    df-fin4
    elab2g
end
