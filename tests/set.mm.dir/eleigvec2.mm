include "chil.mm"
include "wf.mm"
include "cei.mm"
include "cfv.mm"
include "wcel.mm"
include "c0v.mm"
include "wne.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wrex.mm"
include "w3a.mm"
include "csn.mm"
include "cspn.mm"
include "eleigvec.mm"
include "wa.mm"
include "wb.mm"
include "elspansn.mm"
include "adantr.mm"
include "pm5.32i.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "syl6bbr.mm"

theorem eleigvec2
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( T : ~H --> ~H -> ( A e. ( eigvec ` T ) <-> ( A e. ~H /\ A =/= 0h /\ ( T ` A ) e. ( span ` { A } ) ) ) )

  proof
    chil
    chil
    cT
    wf
    cA
    cT
    cei
    cfv
    wcel
    cA
    chil
    wcel
    #
    cA
    c0v
    wne
    #
    cA
    cT
    cfv
    #
    vx
    cv
    cA
    csm
    co
    wceq
    vx
    cc
    wrex
    #
    w3a
    #
    @0
    @1
    @2
    cA
    csn
    cspn
    cfv
    wcel
    #
    w3a
    #
    vx
    cA
    cT
    eleigvec
    @0
    @1
    wa
    #
    @5
    wa
    @7
    @3
    wa
    @6
    @4
    @7
    @5
    @3
    @0
    @5
    @3
    wb
    @1
    vx
    cA
    @2
    elspansn
    adantr
    pm5.32i
    @0
    @1
    @5
    df-3an
    @0
    @1
    @3
    df-3an
    3bitr4i
    syl6bbr
end
