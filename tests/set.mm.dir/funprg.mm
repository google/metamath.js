include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wfun.mm"
include "cpr.mm"
include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "funsng.mm"
include "anim12i.mm"
include "an4s.mm"
include "3adant3.mm"
include "dmsnopg.mm"
include "ineqan12d.mm"
include "disjsn2.mm"
include "sylan9eq.mm"
include "3adant1.mm"
include "funun.mm"
include "syl2anc.mm"
include "df-pr.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem funprg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( ( A e. V /\ B e. W ) /\ ( C e. X /\ D e. Y ) /\ A =/= B ) -> Fun { <. A , C >. , <. B , D >. } )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cC
    cX
    wcel
    #
    cD
    cY
    wcel
    #
    wa
    #
    cA
    cB
    wne
    #
    w3a
    #
    cA
    cC
    cop
    #
    csn
    #
    cB
    cD
    cop
    #
    csn
    #
    cun
    #
    wfun
    #
    @8
    @10
    cpr
    #
    wfun
    @7
    @9
    wfun
    #
    @11
    wfun
    #
    wa
    #
    @9
    cdm
    #
    @11
    cdm
    #
    cin
    #
    c0
    wceq
    #
    @13
    @2
    @5
    @17
    @6
    @0
    @3
    @1
    @4
    @17
    @0
    @3
    wa
    @15
    @1
    @4
    wa
    @16
    cA
    cC
    cV
    cX
    funsng
    cB
    cD
    cW
    cY
    funsng
    anim12i
    an4s
    3adant3
    @5
    @6
    @21
    @2
    @5
    @6
    @20
    cA
    csn
    #
    cB
    csn
    #
    cin
    c0
    @3
    @4
    @18
    @22
    @19
    @23
    cA
    cC
    cX
    dmsnopg
    cB
    cD
    cY
    dmsnopg
    ineqan12d
    cA
    cB
    disjsn2
    sylan9eq
    3adant1
    @9
    @11
    funun
    syl2anc
    @14
    @12
    @8
    @10
    df-pr
    funeqi
    sylibr
end
