include "wcel.mm"
include "cop.mm"
include "cdiag2.mm"
include "cfv.mm"
include "cid.mm"
include "cxp.mm"
include "cin.mm"
include "wceq.mm"
include "wa.mm"
include "bj-diagval.mm"
include "eleq2d.mm"
include "cvv.mm"
include "elin.mm"
include "bj-elid3.mm"
include "opelxp.mm"
include "anbi12i.mm"
include "simprl.mm"
include "simplr.mm"
include "jca.mm"
include "elex.mm"
include "anim1i.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "imdistani.mm"
include "impbii.mm"
include "3bitri.mm"
include "syl6bb.mm"

theorem bj-eldiag2
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( A e. V -> ( <. B , C >. e. ( Diag ` A ) <-> ( B e. A /\ B = C ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cC
    cop
    #
    cA
    cdiag2
    cfv
    #
    wcel
    @1
    cid
    cA
    cA
    cxp
    #
    cin
    #
    wcel
    #
    cB
    cA
    wcel
    #
    cB
    cC
    wceq
    #
    wa
    #
    @0
    @2
    @4
    @1
    cA
    cV
    bj-diagval
    eleq2d
    @5
    @1
    cid
    wcel
    #
    @1
    @3
    wcel
    #
    wa
    cB
    cvv
    wcel
    #
    @7
    wa
    #
    @6
    cC
    cA
    wcel
    #
    wa
    #
    wa
    #
    @8
    @1
    cid
    @3
    elin
    @9
    @12
    @10
    @14
    cB
    cC
    bj-elid3
    cB
    cC
    cA
    cA
    opelxp
    anbi12i
    @15
    @8
    @15
    @6
    @7
    @12
    @6
    @13
    simprl
    @11
    @7
    @14
    simplr
    jca
    @8
    @12
    @14
    @6
    @11
    @7
    cB
    cA
    elex
    anim1i
    @6
    @7
    @13
    @7
    @6
    @13
    cB
    cC
    cA
    eleq1
    biimpcd
    imdistani
    jca
    impbii
    3bitri
    syl6bb
end
