include "word.mm"
include "wa.mm"
include "cun.mm"
include "csuc.mm"
include "cv.mm"
include "con0.mm"
include "wcel.mm"
include "wi.mm"
include "ordun.mm"
include "ordsuc.mm"
include "ordelon.mm"
include "ex.mm"
include "sylbi.mm"
include "syl.mm"
include "syl2anb.mm"
include "wb.mm"
include "wo.mm"
include "wss.mm"
include "ordssun.mm"
include "adantl.mm"
include "ordsssuc.mm"
include "sylan2.mm"
include "adantrr.mm"
include "adantrl.mm"
include "orbi12d.mm"
include "3bitr3d.mm"
include "elun.mm"
include "syl6bbr.mm"
include "expcom.mm"
include "pm5.21ndd.mm"
include "eqrdv.mm"

theorem ordsucun
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( Ord A /\ Ord B ) -> suc ( A u. B ) = ( suc A u. suc B ) )

  proof
    cA
    word
    #
    cB
    word
    #
    wa
    #
    vx
    cA
    cB
    cun
    #
    csuc
    #
    cA
    csuc
    #
    cB
    csuc
    #
    cun
    #
    @2
    vx
    cv
    #
    con0
    wcel
    #
    @8
    @4
    wcel
    #
    @8
    @7
    wcel
    #
    @2
    @3
    word
    #
    @10
    @9
    wi
    #
    cA
    cB
    ordun
    #
    @12
    @4
    word
    #
    @13
    @3
    ordsuc
    @15
    @10
    @9
    @4
    @8
    ordelon
    ex
    sylbi
    syl
    @0
    @5
    word
    #
    @6
    word
    #
    @11
    @9
    wi
    #
    @1
    cA
    ordsuc
    cB
    ordsuc
    @16
    @17
    wa
    @7
    word
    #
    @18
    @5
    @6
    ordun
    @19
    @11
    @9
    @7
    @8
    ordelon
    ex
    syl
    syl2anb
    @9
    @2
    @10
    @11
    wb
    @9
    @2
    wa
    #
    @10
    @8
    @5
    wcel
    #
    @8
    @6
    wcel
    #
    wo
    #
    @11
    @20
    @8
    @3
    wss
    #
    @8
    cA
    wss
    #
    @8
    cB
    wss
    #
    wo
    #
    @10
    @23
    @2
    @24
    @27
    wb
    @9
    @8
    cA
    cB
    ordssun
    adantl
    @2
    @9
    @12
    @24
    @10
    wb
    @14
    @8
    @3
    ordsssuc
    sylan2
    @20
    @25
    @21
    @26
    @22
    @9
    @0
    @25
    @21
    wb
    @1
    @8
    cA
    ordsssuc
    adantrr
    @9
    @1
    @26
    @22
    wb
    @0
    @8
    cB
    ordsssuc
    adantrl
    orbi12d
    3bitr3d
    @8
    @5
    @6
    elun
    syl6bbr
    expcom
    pm5.21ndd
    eqrdv
end
