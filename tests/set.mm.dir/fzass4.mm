include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "simpll.mm"
include "simprl.mm"
include "jca.mm"
include "uztrn.mm"
include "ancoms.mm"
include "ad2ant2r.mm"
include "simprr.mm"
include "jca32.mm"
include "ad2ant2l.mm"
include "simplr.mm"
include "impbii.mm"
include "elfzuzb.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem fzass4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( B e. ( A ... D ) /\ C e. ( B ... D ) ) <-> ( B e. ( A ... C ) /\ C e. ( A ... D ) ) )

  proof
    cB
    cA
    cuz
    cfv
    #
    wcel
    #
    cD
    cB
    cuz
    cfv
    #
    wcel
    #
    wa
    #
    cC
    @2
    wcel
    #
    cD
    cC
    cuz
    cfv
    wcel
    #
    wa
    #
    wa
    #
    @1
    @5
    wa
    #
    cC
    @0
    wcel
    #
    @6
    wa
    #
    wa
    #
    cB
    cA
    cD
    cfz
    co
    #
    wcel
    #
    cC
    cB
    cD
    cfz
    co
    wcel
    #
    wa
    cB
    cA
    cC
    cfz
    co
    wcel
    #
    cC
    @13
    wcel
    #
    wa
    @8
    @12
    @8
    @9
    @10
    @6
    @8
    @1
    @5
    @1
    @3
    @7
    simpll
    @4
    @5
    @6
    simprl
    jca
    @1
    @5
    @10
    @3
    @6
    @5
    @1
    @10
    cB
    cC
    cA
    uztrn
    ancoms
    ad2ant2r
    @4
    @5
    @6
    simprr
    jca32
    @12
    @4
    @5
    @6
    @12
    @1
    @3
    @1
    @5
    @11
    simpll
    @5
    @6
    @3
    @1
    @10
    @6
    @5
    @3
    cC
    cD
    cB
    uztrn
    ancoms
    ad2ant2l
    jca
    @1
    @5
    @11
    simplr
    @9
    @10
    @6
    simprr
    jca32
    impbii
    @14
    @4
    @15
    @7
    cB
    cA
    cD
    elfzuzb
    cC
    cB
    cD
    elfzuzb
    anbi12i
    @16
    @9
    @17
    @11
    cB
    cA
    cC
    elfzuzb
    cC
    cA
    cD
    elfzuzb
    anbi12i
    3bitr4i
end
