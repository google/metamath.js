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
include "wceq.mm"
include "psmetsym.mm"
include "3expb.mm"
include "adantlr.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem elbl3ps
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


  assert |- ( ( ( D e. ( PsMet ` X ) /\ R e. RR* ) /\ ( P e. X /\ A e. X ) ) -> ( A e. ( P ( ball ` D ) R ) <-> ( A D P ) < R ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cR
    cxr
    wcel
    #
    wa
    cP
    cX
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
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
    cP
    cA
    cD
    co
    #
    cR
    clt
    wbr
    cA
    cP
    cD
    co
    #
    cR
    clt
    wbr
    cA
    cD
    cP
    cR
    cX
    elbl2ps
    @5
    @6
    @7
    cR
    clt
    @0
    @4
    @6
    @7
    wceq
    #
    @1
    @0
    @2
    @3
    @8
    cP
    cA
    cD
    cX
    psmetsym
    3expb
    adantlr
    breq1d
    bitrd
end
