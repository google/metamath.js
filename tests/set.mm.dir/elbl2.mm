include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "wa.mm"
include "cbl.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "elbl.mm"
include "3expa.mm"
include "an32s.mm"
include "adantrr.mm"
include "simprr.mm"
include "biantrurd.mm"
include "bitr4d.mm"

theorem elbl2
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cX: class X
  let vx: setvar x
  let vr: setvar r
  let vy: setvar y
  let wph: wff ph
  let cQ: class Q
  let cS: class S


  assert |- ( ( ( D e. ( *Met ` X ) /\ R e. RR* ) /\ ( P e. X /\ A e. X ) ) -> ( A e. ( P ( ball ` D ) R ) <-> ( P D A ) < R ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cR
    cxr
    wcel
    #
    wa
    #
    cP
    cX
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    wa
    #
    cA
    cP
    cR
    cD
    cbl
    cfv
    co
    wcel
    #
    @4
    cP
    cA
    cD
    co
    cR
    clt
    wbr
    #
    wa
    #
    @7
    @2
    @3
    @6
    @8
    wb
    #
    @4
    @0
    @3
    @1
    @9
    @0
    @3
    @1
    @9
    cA
    cD
    cP
    cR
    cX
    elbl
    3expa
    an32s
    adantrr
    @5
    @4
    @7
    @2
    @3
    @4
    simprr
    biantrurd
    bitr4d
end
