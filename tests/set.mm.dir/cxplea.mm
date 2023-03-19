include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "clt.mm"
include "ccxp.mm"
include "co.mm"
include "wceq.mm"
include "simpl3.mm"
include "wb.mm"
include "simpl1l.mm"
include "simpr.mm"
include "simpl2.mm"
include "cxple.mm"
include "syl21anc.mm"
include "mpbid.mm"
include "1le1.mm"
include "cc.mm"
include "simp2l.mm"
include "recnd.mm"
include "1cxp.mm"
include "syl.mm"
include "simp2r.mm"
include "breq12d.mm"
include "mpbiri.mm"
include "oveq1.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "wo.mm"
include "1re.mm"
include "leloe.mm"
include "mpan.mm"
include "biimpa.mm"
include "3ad2ant1.mm"
include "mpjaodan.mm"

theorem cxplea
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ 1 <_ A ) /\ ( B e. RR /\ C e. RR ) /\ B <_ C ) -> ( A ^c B ) <_ ( A ^c C ) )

  proof
    cA
    cr
    wcel
    #
    c1
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
    cC
    cr
    wcel
    #
    wa
    #
    cB
    cC
    cle
    wbr
    #
    w3a
    #
    c1
    cA
    clt
    wbr
    #
    cA
    cB
    ccxp
    co
    #
    cA
    cC
    ccxp
    co
    #
    cle
    wbr
    #
    c1
    cA
    wceq
    #
    @7
    @8
    wa
    #
    @6
    @11
    @2
    @5
    @6
    @8
    simpl3
    @13
    @0
    @8
    @5
    @6
    @11
    wb
    @0
    @1
    @5
    @6
    @8
    simpl1l
    @7
    @8
    simpr
    @2
    @5
    @6
    @8
    simpl2
    cA
    cB
    cC
    cxple
    syl21anc
    mpbid
    @7
    @12
    @11
    @7
    c1
    cB
    ccxp
    co
    #
    c1
    cC
    ccxp
    co
    #
    cle
    wbr
    #
    @12
    @11
    @7
    @16
    c1
    c1
    cle
    wbr
    1le1
    @7
    @14
    c1
    @15
    c1
    cle
    @7
    cB
    cc
    wcel
    @14
    c1
    wceq
    @7
    cB
    @2
    @3
    @4
    @6
    simp2l
    recnd
    cB
    1cxp
    syl
    @7
    cC
    cc
    wcel
    @15
    c1
    wceq
    @7
    cC
    @2
    @3
    @4
    @6
    simp2r
    recnd
    cC
    1cxp
    syl
    breq12d
    mpbiri
    @12
    @14
    @9
    @15
    @10
    cle
    c1
    cA
    cB
    ccxp
    oveq1
    c1
    cA
    cC
    ccxp
    oveq1
    breq12d
    syl5ibcom
    imp
    @2
    @5
    @8
    @12
    wo
    #
    @6
    @0
    @1
    @17
    c1
    cr
    wcel
    @0
    @1
    @17
    wb
    1re
    c1
    cA
    leloe
    mpan
    biimpa
    3ad2ant1
    mpjaodan
end
