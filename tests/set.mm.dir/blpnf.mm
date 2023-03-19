include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cpnf.mm"
include "cbl.mm"
include "co.mm"
include "cv.mm"
include "cr.mm"
include "cxmt.mm"
include "wb.mm"
include "metxmet.mm"
include "xblpnf.mm"
include "sylan.mm"
include "metcl.mm"
include "3expia.mm"
include "pm4.71d.mm"
include "bitr4d.mm"
include "eqrdv.mm"

theorem blpnf
  let cD: class D
  let cP: class P
  let cX: class X
  let cA: class A
  let vx: setvar x
  let vr: setvar r
  let vy: setvar y
  let wph: wff ph
  let cQ: class Q
  let cS: class S
  let cR: class R


  assert |- ( ( D e. ( Met ` X ) /\ P e. X ) -> ( P ( ball ` D ) +oo ) = X )

  proof
    cD
    cX
    cme
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    #
    vx
    cP
    cpnf
    cD
    cbl
    cfv
    co
    #
    cX
    @2
    vx
    cv
    #
    @3
    wcel
    #
    @4
    cX
    wcel
    #
    cP
    @4
    cD
    co
    cr
    wcel
    #
    wa
    #
    @6
    @0
    cD
    cX
    cxmt
    cfv
    wcel
    @1
    @5
    @8
    wb
    cD
    cX
    metxmet
    @4
    cD
    cP
    cX
    xblpnf
    sylan
    @2
    @6
    @7
    @0
    @1
    @6
    @7
    cP
    @4
    cD
    cX
    metcl
    3expia
    pm4.71d
    bitr4d
    eqrdv
end
