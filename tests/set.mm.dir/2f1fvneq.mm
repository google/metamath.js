include "wf1.mm"
include "wa.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wn.mm"
include "wi.mm"
include "f1veqaeq.mm"
include "adantll.mm"
include "necon3ad.mm"
include "3impia.mm"
include "simpll.mm"
include "wf.mm"
include "f1f.mm"
include "ffvelrn.mm"
include "anim12dan.mm"
include "ex.mm"
include "syl.mm"
include "adantl.mm"
include "imp.mm"
include "syl2anc.mm"
include "con3dimp.mm"
include "eqeq12.mm"
include "notbid.mm"
include "df-ne.mm"
include "biimpri.mm"
include "syl6bi.mm"
include "syl5com.mm"
include "3adant3.mm"
include "mpd.mm"

theorem 2f1fvneq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cE: class E
  let cF: class F
  let cX: class X
  let cY: class Y


  assert |- ( ( ( E : D -1-1-> R /\ F : C -1-1-> D ) /\ ( A e. C /\ B e. C ) /\ A =/= B ) -> ( ( ( E ` ( F ` A ) ) = X /\ ( E ` ( F ` B ) ) = Y ) -> X =/= Y ) )

  proof
    cD
    cR
    cE
    wf1
    #
    cC
    cD
    cF
    wf1
    #
    wa
    #
    cA
    cC
    wcel
    #
    cB
    cC
    wcel
    #
    wa
    #
    cA
    cB
    wne
    #
    w3a
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    wceq
    #
    wn
    #
    @7
    cE
    cfv
    #
    cX
    wceq
    @8
    cE
    cfv
    #
    cY
    wceq
    wa
    #
    cX
    cY
    wne
    #
    wi
    #
    @2
    @5
    @6
    @10
    @2
    @5
    wa
    #
    @9
    cA
    cB
    @1
    @5
    @9
    cA
    cB
    wceq
    wi
    @0
    cC
    cD
    cA
    cB
    cF
    f1veqaeq
    adantll
    necon3ad
    3impia
    @2
    @5
    @10
    @15
    wi
    @6
    @16
    @10
    @15
    @16
    @10
    wa
    @11
    @12
    wceq
    #
    wn
    #
    @13
    @14
    @16
    @17
    @9
    @16
    @0
    @7
    cD
    wcel
    #
    @8
    cD
    wcel
    #
    wa
    #
    @17
    @9
    wi
    @0
    @1
    @5
    simpll
    @2
    @5
    @21
    @1
    @5
    @21
    wi
    #
    @0
    @1
    cC
    cD
    cF
    wf
    #
    @22
    cC
    cD
    cF
    f1f
    @23
    @5
    @21
    @23
    @3
    @19
    @4
    @20
    cC
    cD
    cA
    cF
    ffvelrn
    cC
    cD
    cB
    cF
    ffvelrn
    anim12dan
    ex
    syl
    adantl
    imp
    cD
    cR
    @7
    @8
    cE
    f1veqaeq
    syl2anc
    con3dimp
    @13
    @18
    cX
    cY
    wceq
    #
    wn
    #
    @14
    @13
    @17
    @24
    @11
    cX
    @12
    cY
    eqeq12
    notbid
    @14
    @25
    cX
    cY
    df-ne
    biimpri
    syl6bi
    syl5com
    ex
    3adant3
    mpd
end
