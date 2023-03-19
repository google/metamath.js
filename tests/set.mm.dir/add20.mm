include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "simpllr.mm"
include "wb.mm"
include "simplrl.mm"
include "simplll.mm"
include "addge02.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simpr.mm"
include "breqtrd.mm"
include "simplrr.mm"
include "0red.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "oveq2d.mm"
include "recnd.mm"
include "addid1d.mm"
include "3eqtr3rd.mm"
include "jca.mm"
include "ex.mm"
include "oveq12.mm"
include "00id.mm"
include "syl6eq.mm"
include "impbid1.mm"

theorem add20
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> ( ( A + B ) = 0 <-> ( A = 0 /\ B = 0 ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    caddc
    co
    #
    cc0
    wceq
    #
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    wa
    #
    @6
    @8
    @11
    @6
    @8
    wa
    #
    @9
    @10
    @12
    @7
    cA
    cc0
    caddc
    co
    cc0
    cA
    @12
    cB
    cc0
    cA
    caddc
    @12
    @10
    cB
    cc0
    cle
    wbr
    @4
    @12
    cB
    @7
    cc0
    cle
    @12
    @1
    cB
    @7
    cle
    wbr
    #
    @0
    @1
    @5
    @8
    simpllr
    @12
    @3
    @0
    @1
    @13
    wb
    @2
    @3
    @4
    @8
    simplrl
    #
    @0
    @1
    @5
    @8
    simplll
    #
    cB
    cA
    addge02
    syl2anc
    mpbid
    @6
    @8
    simpr
    #
    breqtrd
    @2
    @3
    @4
    @8
    simplrr
    @12
    cB
    cc0
    @14
    @12
    0red
    letri3d
    mpbir2and
    #
    oveq2d
    @16
    @12
    cA
    @12
    cA
    @15
    recnd
    addid1d
    3eqtr3rd
    @17
    jca
    ex
    @11
    @7
    cc0
    cc0
    caddc
    co
    cc0
    cA
    cc0
    cB
    cc0
    caddc
    oveq12
    00id
    syl6eq
    impbid1
end
