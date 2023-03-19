include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "cint.mm"
include "cin.mm"
include "wceq.mm"
include "intprg.mm"
include "3adant1.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "simp1.mm"
include "prssi.mm"
include "prnzg.mm"
include "3ad2ant2.mm"
include "mreintcl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"

theorem mreincl
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X
  let vc: setvar c
  let vs: setvar s
  let vx: setvar x
  let cS: class S
  let cI: class I
  let vy: setvar y


  assert |- ( ( C e. ( Moore ` X ) /\ A e. C /\ B e. C ) -> ( A i^i B ) e. C )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cA
    cC
    wcel
    #
    cB
    cC
    wcel
    #
    w3a
    #
    cA
    cB
    cpr
    #
    cint
    #
    cA
    cB
    cin
    #
    cC
    @1
    @2
    @5
    @6
    wceq
    @0
    cA
    cB
    cC
    cC
    intprg
    3adant1
    @3
    @0
    @4
    cC
    wss
    #
    @4
    c0
    wne
    #
    @5
    cC
    wcel
    @0
    @1
    @2
    simp1
    @1
    @2
    @7
    @0
    cA
    cB
    cC
    prssi
    3adant1
    @1
    @0
    @8
    @2
    cA
    cB
    cC
    prnzg
    3ad2ant2
    cC
    @4
    cX
    mreintcl
    syl3anc
    eqeltrrd
end
