include "wcel.mm"
include "csuc.mm"
include "cin.mm"
include "csn.mm"
include "cun.mm"
include "df-suc.mm"
include "ineq2i.mm"
include "indi.mm"
include "uncom.mm"
include "3eqtri.mm"
include "wss.mm"
include "wceq.mm"
include "snssi.mm"
include "sseqin2.mm"
include "sylib.mm"
include "uneq1d.mm"
include "syl5eq.mm"

theorem ackbij1lem2
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cH: class H


  assert |- ( A e. B -> ( B i^i suc A ) = ( { A } u. ( B i^i A ) ) )

  proof
    cA
    cB
    wcel
    #
    cB
    cA
    csuc
    #
    cin
    #
    cB
    cA
    csn
    #
    cin
    #
    cB
    cA
    cin
    #
    cun
    #
    @3
    @5
    cun
    @2
    cB
    cA
    @3
    cun
    #
    cin
    @5
    @4
    cun
    @6
    @1
    @7
    cB
    cA
    df-suc
    ineq2i
    cB
    cA
    @3
    indi
    @5
    @4
    uncom
    3eqtri
    @0
    @4
    @3
    @5
    @0
    @3
    cB
    wss
    @4
    @3
    wceq
    cA
    cB
    snssi
    @3
    cB
    sseqin2
    sylib
    uneq1d
    syl5eq
end
