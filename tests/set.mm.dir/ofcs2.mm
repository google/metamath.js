include "wcel.mm"
include "w3a.mm"
include "cs2.mm"
include "cofc.mm"
include "co.mm"
include "cs1.mm"
include "cconcat.mm"
include "df-s2.mm"
include "oveq1i.mm"
include "simp1.mm"
include "s1cld.mm"
include "simp2.mm"
include "simp3.mm"
include "ofcccat.mm"
include "syl5eq.mm"
include "wceq.mm"
include "ofcs1.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "syl6eqr.mm"
include "eqtrd.mm"

theorem ofcs2
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T


  assert |- ( ( A e. S /\ B e. S /\ C e. T ) -> ( <" A B "> oFC R C ) = <" ( A R C ) ( B R C ) "> )

  proof
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    cC
    cT
    wcel
    #
    w3a
    #
    cA
    cB
    cs2
    #
    cC
    cR
    cofc
    #
    co
    #
    cA
    cs1
    #
    cC
    @5
    co
    #
    cB
    cs1
    #
    cC
    @5
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
    cC
    cR
    co
    #
    cs2
    #
    @3
    @6
    @7
    @9
    cconcat
    co
    #
    cC
    @5
    co
    @11
    @4
    @15
    cC
    @5
    cA
    cB
    df-s2
    oveq1i
    @3
    cR
    cS
    cT
    @7
    @9
    cC
    @3
    cA
    cS
    @0
    @1
    @2
    simp1
    #
    s1cld
    @3
    cB
    cS
    @0
    @1
    @2
    simp2
    #
    s1cld
    @0
    @1
    @2
    simp3
    #
    ofcccat
    syl5eq
    @3
    @11
    @12
    cs1
    #
    @13
    cs1
    #
    cconcat
    co
    @14
    @3
    @8
    @19
    @10
    @20
    cconcat
    @3
    @0
    @2
    @8
    @19
    wceq
    @16
    @18
    cA
    cC
    cR
    cS
    cT
    ofcs1
    syl2anc
    @3
    @1
    @2
    @10
    @20
    wceq
    @17
    @18
    cB
    cC
    cR
    cS
    cT
    ofcs1
    syl2anc
    oveq12d
    @12
    @13
    df-s2
    syl6eqr
    eqtrd
end
