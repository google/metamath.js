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
include "simp1l.mm"
include "simp2l.mm"
include "funsng.mm"
include "syl2anc.mm"
include "simp1r.mm"
include "simp2r.mm"
include "dmsnopg.mm"
include "syl.mm"
include "ineq12d.mm"
include "disjsn2.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"
include "funun.mm"
include "syl21anc.mm"
include "df-pr.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem funprgOLD
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
    @13
    @7
    @0
    @3
    @15
    @0
    @1
    @5
    @6
    simp1l
    @2
    @3
    @4
    @6
    simp2l
    #
    cA
    cC
    cV
    cX
    funsng
    syl2anc
    @7
    @1
    @4
    @16
    @0
    @1
    @5
    @6
    simp1r
    @2
    @3
    @4
    @6
    simp2r
    #
    cB
    cD
    cW
    cY
    funsng
    syl2anc
    @7
    @19
    cA
    csn
    #
    cB
    csn
    #
    cin
    #
    c0
    @7
    @17
    @22
    @18
    @23
    @7
    @3
    @17
    @22
    wceq
    @20
    cA
    cC
    cX
    dmsnopg
    syl
    @7
    @4
    @18
    @23
    wceq
    @21
    cB
    cD
    cY
    dmsnopg
    syl
    ineq12d
    @6
    @2
    @24
    c0
    wceq
    @5
    cA
    cB
    disjsn2
    3ad2ant3
    eqtrd
    @9
    @11
    funun
    syl21anc
    @14
    @12
    @8
    @10
    df-pr
    funeqi
    sylibr
end
