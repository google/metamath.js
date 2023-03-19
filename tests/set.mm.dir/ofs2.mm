include "wcel.mm"
include "wa.mm"
include "cs2.mm"
include "cof.mm"
include "co.mm"
include "cs1.mm"
include "cconcat.mm"
include "df-s2.mm"
include "oveq12i.mm"
include "simpll.mm"
include "s1cld.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "s1len.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "ofccat.mm"
include "syl5eq.mm"
include "ofs1.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "syl6eqr.mm"
include "eqtrd.mm"

theorem ofs2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cT: class T


  assert |- ( ( ( A e. S /\ B e. S ) /\ ( C e. T /\ D e. T ) ) -> ( <" A B "> oF R <" C D "> ) = <" ( A R C ) ( B R D ) "> )

  proof
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    wa
    #
    cC
    cT
    wcel
    #
    cD
    cT
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cs2
    #
    cC
    cD
    cs2
    #
    cR
    cof
    #
    co
    #
    cA
    cs1
    #
    cC
    cs1
    #
    @9
    co
    #
    cB
    cs1
    #
    cD
    cs1
    #
    @9
    co
    #
    cconcat
    co
    #
    cA
    cC
    cR
    co
    #
    cB
    cD
    cR
    co
    #
    cs2
    #
    @6
    @10
    @11
    @14
    cconcat
    co
    #
    @12
    @15
    cconcat
    co
    #
    @9
    co
    @17
    @7
    @21
    @8
    @22
    @9
    cA
    cB
    df-s2
    cC
    cD
    df-s2
    oveq12i
    @6
    cR
    cS
    cT
    @11
    @14
    @12
    @15
    @6
    cA
    cS
    @0
    @1
    @5
    simpll
    #
    s1cld
    @6
    cB
    cS
    @0
    @1
    @5
    simplr
    #
    s1cld
    @6
    cC
    cT
    @2
    @3
    @4
    simprl
    #
    s1cld
    @6
    cD
    cT
    @2
    @3
    @4
    simprr
    #
    s1cld
    @11
    chash
    cfv
    #
    @12
    chash
    cfv
    #
    wceq
    @6
    @27
    c1
    @28
    cA
    s1len
    cC
    s1len
    eqtr4i
    a1i
    @14
    chash
    cfv
    #
    @15
    chash
    cfv
    #
    wceq
    @6
    @29
    c1
    @30
    cB
    s1len
    cD
    s1len
    eqtr4i
    a1i
    ofccat
    syl5eq
    @6
    @17
    @18
    cs1
    #
    @19
    cs1
    #
    cconcat
    co
    @20
    @6
    @13
    @31
    @16
    @32
    cconcat
    @6
    @0
    @3
    @13
    @31
    wceq
    @23
    @25
    cA
    cC
    cR
    cS
    cT
    ofs1
    syl2anc
    @6
    @1
    @4
    @16
    @32
    wceq
    @24
    @26
    cB
    cD
    cR
    cS
    cT
    ofs1
    syl2anc
    oveq12d
    @18
    @19
    df-s2
    syl6eqr
    eqtrd
end
