include "con0.mm"
include "wss.mm"
include "wcel.mm"
include "cv.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "cint.mm"
include "wceq.mm"
include "ssint.mm"
include "wi.mm"
include "wb.mm"
include "ssel.mm"
include "anim12d.mm"
include "ontri1.mm"
include "syl6.mm"
include "expdimp.mm"
include "pm5.74d.mm"
include "con2b.mm"
include "syl6bb.mm"
include "ralbidv2.mm"
include "syl5bb.mm"
include "biimprd.mm"
include "expimpd.mm"
include "intss1.mm"
include "a1i.mm"
include "adantrd.mm"
include "jcad.mm"
include "eqss.mm"
include "syl6ibr.mm"

theorem oneqmini
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( B C_ On -> ( ( A e. B /\ A. x e. A -. x e. B ) -> A = |^| B ) )

  proof
    cB
    con0
    wss
    #
    cA
    cB
    wcel
    #
    vx
    cv
    #
    cB
    wcel
    #
    wn
    #
    vx
    cA
    wral
    #
    wa
    #
    cA
    cB
    cint
    #
    wss
    #
    @7
    cA
    wss
    #
    wa
    cA
    @7
    wceq
    @0
    @6
    @8
    @9
    @0
    @1
    @5
    @8
    @0
    @1
    wa
    #
    @8
    @5
    @8
    cA
    @2
    wss
    #
    vx
    cB
    wral
    @10
    @5
    vx
    cA
    cB
    ssint
    @10
    @11
    @4
    vx
    cB
    cA
    @10
    @3
    @11
    wi
    @3
    @2
    cA
    wcel
    #
    wn
    #
    wi
    @12
    @4
    wi
    @10
    @3
    @11
    @13
    @0
    @1
    @3
    @11
    @13
    wb
    #
    @0
    @1
    @3
    wa
    cA
    con0
    wcel
    #
    @2
    con0
    wcel
    #
    wa
    @14
    @0
    @1
    @15
    @3
    @16
    cB
    con0
    cA
    ssel
    cB
    con0
    @2
    ssel
    anim12d
    cA
    @2
    ontri1
    syl6
    expdimp
    pm5.74d
    @3
    @12
    con2b
    syl6bb
    ralbidv2
    syl5bb
    biimprd
    expimpd
    @0
    @1
    @9
    @5
    @1
    @9
    wi
    @0
    cA
    cB
    intss1
    a1i
    adantrd
    jcad
    cA
    @7
    eqss
    syl6ibr
end
