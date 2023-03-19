include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "wa.mm"
include "cbl.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "elbl2ps.mm"
include "wb.mm"
include "elbl3ps.mm"
include "ancom2s.mm"
include "bitr4d.mm"

theorem blcomps
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


  assert |- ( ( ( D e. ( PsMet ` X ) /\ R e. RR* ) /\ ( P e. X /\ A e. X ) ) -> ( A e. ( P ( ball ` D ) R ) <-> P e. ( A ( ball ` D ) R ) ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    cR
    cxr
    wcel
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
    cA
    cP
    cR
    cD
    cbl
    cfv
    #
    co
    wcel
    cP
    cA
    cD
    co
    cR
    clt
    wbr
    #
    cP
    cA
    cR
    @3
    co
    wcel
    #
    cA
    cD
    cP
    cR
    cX
    elbl2ps
    @0
    @2
    @1
    @5
    @4
    wb
    cP
    cD
    cA
    cR
    cX
    elbl3ps
    ancom2s
    bitr4d
end
