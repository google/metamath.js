include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cconcat.mm"
include "co.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "oveq1.mm"
include "swrdccat1.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "3ad2ant2.mm"
include "eqtrd.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "caddc.mm"
include "simpr.mm"
include "simpl3.mm"
include "fveq2d.mm"
include "simpl1.mm"
include "ccatlen.mm"
include "syl.mm"
include "simpl2.mm"
include "3eqtr3d.mm"
include "opeq12d.mm"
include "oveq12d.mm"
include "swrdccat2.mm"
include "ex.mm"
include "jcad.mm"
include "oveq12.mm"
include "impbid1.mm"

theorem ccatopth
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X


  assert |- ( ( ( A e. Word X /\ B e. Word X ) /\ ( C e. Word X /\ D e. Word X ) /\ ( # ` A ) = ( # ` C ) ) -> ( ( A ++ B ) = ( C ++ D ) <-> ( A = C /\ B = D ) ) )

  proof
    cA
    cX
    cword
    #
    wcel
    cB
    @0
    wcel
    wa
    #
    cC
    @0
    wcel
    cD
    @0
    wcel
    wa
    #
    cA
    chash
    cfv
    #
    cC
    chash
    cfv
    #
    wceq
    #
    w3a
    #
    cA
    cB
    cconcat
    co
    #
    cC
    cD
    cconcat
    co
    #
    wceq
    #
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    @6
    @9
    @10
    @11
    @9
    @7
    cc0
    @3
    cop
    #
    csubstr
    co
    #
    @8
    @12
    csubstr
    co
    #
    wceq
    @6
    @10
    @7
    @8
    @12
    csubstr
    oveq1
    @6
    @13
    cA
    @14
    cC
    @1
    @2
    @13
    cA
    wceq
    @5
    cX
    cA
    cB
    swrdccat1
    3ad2ant1
    @6
    @14
    @8
    cc0
    @4
    cop
    #
    csubstr
    co
    #
    cC
    @6
    @12
    @15
    @8
    csubstr
    @6
    @3
    @4
    cc0
    @1
    @2
    @5
    simp3
    opeq2d
    oveq2d
    @2
    @1
    @16
    cC
    wceq
    @5
    cX
    cC
    cD
    swrdccat1
    3ad2ant2
    eqtrd
    eqeq12d
    syl5ib
    @6
    @9
    @11
    @6
    @9
    wa
    #
    @7
    @3
    @3
    cB
    chash
    cfv
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    @8
    @4
    @4
    cD
    chash
    cfv
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    cB
    cD
    @17
    @7
    @8
    @19
    @22
    csubstr
    @6
    @9
    simpr
    #
    @17
    @3
    @4
    @18
    @21
    @1
    @2
    @5
    @9
    simpl3
    @17
    @7
    chash
    cfv
    #
    @8
    chash
    cfv
    #
    @18
    @21
    @17
    @7
    @8
    chash
    @24
    fveq2d
    @17
    @1
    @25
    @18
    wceq
    @1
    @2
    @5
    @9
    simpl1
    #
    cX
    cA
    cB
    ccatlen
    syl
    @17
    @2
    @26
    @21
    wceq
    @1
    @2
    @5
    @9
    simpl2
    #
    cX
    cC
    cD
    ccatlen
    syl
    3eqtr3d
    opeq12d
    oveq12d
    @17
    @1
    @20
    cB
    wceq
    @27
    cX
    cA
    cB
    swrdccat2
    syl
    @17
    @2
    @23
    cD
    wceq
    @28
    cX
    cC
    cD
    swrdccat2
    syl
    3eqtr3d
    ex
    jcad
    cA
    cC
    cB
    cD
    cconcat
    oveq12
    impbid1
end
