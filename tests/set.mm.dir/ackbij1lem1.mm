include "wcel.mm"
include "wn.mm"
include "csuc.mm"
include "cin.mm"
include "csn.mm"
include "cun.mm"
include "df-suc.mm"
include "ineq2i.mm"
include "indi.mm"
include "eqtri.mm"
include "c0.mm"
include "wceq.mm"
include "disjsn.mm"
include "biimpri.mm"
include "uneq2d.mm"
include "un0.mm"
include "syl6eq.mm"
include "syl5eq.mm"

theorem ackbij1lem1
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


  assert |- ( -. A e. B -> ( B i^i suc A ) = ( B i^i A ) )

  proof
    cA
    cB
    wcel
    wn
    #
    cB
    cA
    csuc
    #
    cin
    #
    cB
    cA
    cin
    #
    cB
    cA
    csn
    #
    cin
    #
    cun
    #
    @3
    @2
    cB
    cA
    @4
    cun
    #
    cin
    @6
    @1
    @7
    cB
    cA
    df-suc
    ineq2i
    cB
    cA
    @4
    indi
    eqtri
    @0
    @6
    @3
    c0
    cun
    @3
    @0
    @5
    c0
    @3
    @5
    c0
    wceq
    @0
    cB
    cA
    disjsn
    biimpri
    uneq2d
    @3
    un0
    syl6eq
    syl5eq
end
