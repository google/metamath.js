include "cr1.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "cfv.mm"
include "con0.mm"
include "wb.mm"
include "wlim.mm"
include "word.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limord.mm"
include "ordsson.mm"
include "mp2b.mm"
include "sseli.mm"
include "onsseleq.mm"
include "syl2an.mm"
include "wi.mm"
include "r1ordg.mm"
include "adantl.mm"
include "wtr.mm"
include "r1tr.mm"
include "trss.mm"
include "ax-mp.mm"
include "syl6.mm"
include "fveq2.mm"
include "eqimss.mm"
include "syl.mm"
include "a1i.mm"
include "jaod.mm"
include "sylbid.mm"

theorem r1ord3g
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom R1 /\ B e. dom R1 ) -> ( A C_ B -> ( R1 ` A ) C_ ( R1 ` B ) ) )

  proof
    cA
    cr1
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cB
    wss
    #
    cA
    cB
    wcel
    #
    cA
    cB
    wceq
    #
    wo
    #
    cA
    cr1
    cfv
    #
    cB
    cr1
    cfv
    #
    wss
    #
    @1
    cA
    con0
    wcel
    cB
    con0
    wcel
    @4
    @7
    wb
    @2
    @0
    con0
    cA
    @0
    wlim
    #
    @0
    word
    @0
    con0
    wss
    cr1
    wfun
    @11
    r1funlim
    simpri
    @0
    limord
    @0
    ordsson
    mp2b
    #
    sseli
    @0
    con0
    cB
    @12
    sseli
    cA
    cB
    onsseleq
    syl2an
    @3
    @5
    @10
    @6
    @3
    @5
    @8
    @9
    wcel
    #
    @10
    @2
    @5
    @13
    wi
    @1
    cA
    cB
    r1ordg
    adantl
    @9
    wtr
    @13
    @10
    wi
    cB
    r1tr
    @9
    @8
    trss
    ax-mp
    syl6
    @6
    @10
    wi
    @3
    @6
    @8
    @9
    wceq
    @10
    cA
    cB
    cr1
    fveq2
    @8
    @9
    eqimss
    syl
    a1i
    jaod
    sylbid
end
