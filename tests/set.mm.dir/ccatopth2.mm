include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cconcat.mm"
include "co.mm"
include "fveq2.mm"
include "caddc.mm"
include "ccatlen.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3ad2ant2.mm"
include "eqeq12d.mm"
include "cn0.mm"
include "simp1l.mm"
include "lencl.mm"
include "syl.mm"
include "nn0cnd.mm"
include "simp2l.mm"
include "simp2r.mm"
include "addcan2d.mm"
include "bitrd.mm"
include "syl5ib.mm"
include "wi.mm"
include "ccatopth.mm"
include "biimpd.mm"
include "3expia.mm"
include "com23.mm"
include "3adant3.mm"
include "mpdd.mm"
include "oveq12.mm"
include "impbid1.mm"

theorem ccatopth2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X


  assert |- ( ( ( A e. Word X /\ B e. Word X ) /\ ( C e. Word X /\ D e. Word X ) /\ ( # ` B ) = ( # ` D ) ) -> ( ( A ++ B ) = ( C ++ D ) <-> ( A = C /\ B = D ) ) )

  proof
    cA
    cX
    cword
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cC
    @0
    wcel
    #
    cD
    @0
    wcel
    #
    wa
    #
    cB
    chash
    cfv
    #
    cD
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
    cB
    cD
    wceq
    wa
    #
    @10
    @13
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
    @14
    @13
    @11
    chash
    cfv
    #
    @12
    chash
    cfv
    #
    wceq
    #
    @10
    @17
    @11
    @12
    chash
    fveq2
    @10
    @20
    @15
    @8
    caddc
    co
    #
    @16
    @8
    caddc
    co
    #
    wceq
    @17
    @10
    @18
    @21
    @19
    @22
    @10
    @18
    @15
    @7
    caddc
    co
    #
    @21
    @3
    @6
    @18
    @23
    wceq
    @9
    cX
    cA
    cB
    ccatlen
    3ad2ant1
    @10
    @7
    @8
    @15
    caddc
    @3
    @6
    @9
    simp3
    oveq2d
    eqtrd
    @6
    @3
    @19
    @22
    wceq
    @9
    cX
    cC
    cD
    ccatlen
    3ad2ant2
    eqeq12d
    @10
    @15
    @16
    @8
    @10
    @15
    @10
    @1
    @15
    cn0
    wcel
    @1
    @2
    @6
    @9
    simp1l
    cX
    cA
    lencl
    syl
    nn0cnd
    @10
    @16
    @10
    @4
    @16
    cn0
    wcel
    @3
    @4
    @5
    @9
    simp2l
    cX
    cC
    lencl
    syl
    nn0cnd
    @10
    @8
    @10
    @5
    @8
    cn0
    wcel
    @3
    @4
    @5
    @9
    simp2r
    cX
    cD
    lencl
    syl
    nn0cnd
    addcan2d
    bitrd
    syl5ib
    @3
    @6
    @13
    @17
    @14
    wi
    wi
    @9
    @3
    @6
    wa
    @17
    @13
    @14
    @3
    @6
    @17
    @13
    @14
    wi
    @3
    @6
    @17
    w3a
    @13
    @14
    cA
    cB
    cC
    cD
    cX
    ccatopth
    biimpd
    3expia
    com23
    3adant3
    mpdd
    cA
    cC
    cB
    cD
    cconcat
    oveq12
    impbid1
end
