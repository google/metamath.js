include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cbl.mm"
include "co.mm"
include "simp2.mm"
include "wceq.mm"
include "xmet0.mm"
include "3adant3.mm"
include "simp3r.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "elbl.mm"
include "3adant3r.mm"
include "mpbir2and.mm"

theorem xblcntr
  let cD: class D
  let cP: class P
  let cR: class R
  let cX: class X
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( D e. ( *Met ` X ) /\ P e. X /\ ( R e. RR* /\ 0 < R ) ) -> P e. ( P ( ball ` D ) R ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cR
    cxr
    wcel
    #
    cc0
    cR
    clt
    wbr
    #
    wa
    #
    w3a
    #
    cP
    cP
    cR
    cD
    cbl
    cfv
    co
    wcel
    #
    @1
    cP
    cP
    cD
    co
    #
    cR
    clt
    wbr
    #
    @0
    @1
    @4
    simp2
    @5
    @7
    cc0
    cR
    clt
    @0
    @1
    @7
    cc0
    wceq
    @4
    cP
    cD
    cX
    xmet0
    3adant3
    @0
    @1
    @2
    @3
    simp3r
    eqbrtrd
    @0
    @1
    @2
    @6
    @1
    @8
    wa
    wb
    @3
    cP
    cD
    cP
    cR
    cX
    elbl
    3adant3r
    mpbir2and
end
