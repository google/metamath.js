include "wfr.mm"
include "cv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "cpred.mm"
include "dffr3.mm"
include "df-pred.mm"
include "eqeq1i.mm"
include "rexbii.mm"
include "imbi2i.mm"
include "albii.mm"
include "bitr4i.mm"

theorem dffr4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R x
  disjoint R y
  assert |- ( R Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) -> E. y e. x Pred ( R , x , y ) = (/) ) )

  proof
    cA
    cR
    wfr
    vx
    cv
    #
    cA
    wss
    @0
    c0
    wne
    wa
    #
    @0
    cR
    ccnv
    vy
    cv
    #
    csn
    cima
    cin
    #
    c0
    wceq
    #
    vy
    @0
    wrex
    #
    wi
    #
    vx
    wal
    @1
    @0
    cR
    @2
    cpred
    #
    c0
    wceq
    #
    vy
    @0
    wrex
    #
    wi
    #
    vx
    wal
    vx
    vy
    cA
    cR
    dffr3
    @10
    @6
    vx
    @9
    @5
    @1
    @8
    @4
    vy
    @0
    @7
    @3
    c0
    @0
    cR
    @2
    df-pred
    eqeq1i
    rexbii
    imbi2i
    albii
    bitr4i
end
