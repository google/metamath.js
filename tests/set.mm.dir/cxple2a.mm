include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "ccxp.mm"
include "co.mm"
include "wceq.mm"
include "simpl3.mm"
include "crp.mm"
include "wb.mm"
include "simp11.mm"
include "adantr.mm"
include "simpl2l.mm"
include "simp12.mm"
include "0red.mm"
include "letrd.mm"
include "simp13.mm"
include "anim1i.mm"
include "elrp.mm"
include "sylibr.mm"
include "cxple2.mm"
include "syl221anc.mm"
include "mpbid.mm"
include "c1.mm"
include "1le1.mm"
include "a1i.mm"
include "cc.mm"
include "recnd.mm"
include "cxp0.mm"
include "syl.mm"
include "oveq2.mm"
include "sylan9req.mm"
include "3brtr3d.mm"
include "wo.mm"
include "simp2r.mm"
include "0re.mm"
include "leloe.mm"
include "sylancr.mm"
include "mpjaodan.mm"

theorem cxple2a
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ B e. RR /\ C e. RR ) /\ ( 0 <_ A /\ 0 <_ C ) /\ A <_ B ) -> ( A ^c C ) <_ ( B ^c C ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    #
    cc0
    cA
    cle
    wbr
    #
    cc0
    cC
    cle
    wbr
    #
    wa
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    cc0
    cC
    clt
    wbr
    #
    cA
    cC
    ccxp
    co
    #
    cB
    cC
    ccxp
    co
    #
    cle
    wbr
    #
    cc0
    cC
    wceq
    #
    @8
    @9
    wa
    #
    @7
    @12
    @3
    @6
    @7
    @9
    simpl3
    #
    @14
    @0
    @4
    @1
    cc0
    cB
    cle
    wbr
    cC
    crp
    wcel
    #
    @7
    @12
    wb
    @8
    @0
    @9
    @0
    @1
    @2
    @6
    @7
    simp11
    #
    adantr
    #
    @4
    @5
    @3
    @7
    @9
    simpl2l
    #
    @8
    @1
    @9
    @0
    @1
    @2
    @6
    @7
    simp12
    #
    adantr
    #
    @14
    cc0
    cA
    cB
    @14
    0red
    @18
    @21
    @19
    @15
    letrd
    @14
    @2
    @9
    wa
    @16
    @8
    @2
    @9
    @0
    @1
    @2
    @6
    @7
    simp13
    #
    anim1i
    cC
    elrp
    sylibr
    cA
    cB
    cC
    cxple2
    syl221anc
    mpbid
    @8
    @13
    wa
    #
    c1
    c1
    @10
    @11
    cle
    c1
    c1
    cle
    wbr
    @23
    1le1
    a1i
    @8
    @13
    c1
    cA
    cc0
    ccxp
    co
    #
    @10
    @8
    cA
    cc
    wcel
    @24
    c1
    wceq
    @8
    cA
    @17
    recnd
    cA
    cxp0
    syl
    cc0
    cC
    cA
    ccxp
    oveq2
    sylan9req
    @8
    @13
    c1
    cB
    cc0
    ccxp
    co
    #
    @11
    @8
    cB
    cc
    wcel
    @25
    c1
    wceq
    @8
    cB
    @20
    recnd
    cB
    cxp0
    syl
    cc0
    cC
    cB
    ccxp
    oveq2
    sylan9req
    3brtr3d
    @8
    @5
    @9
    @13
    wo
    #
    @3
    @4
    @5
    @7
    simp2r
    @8
    cc0
    cr
    wcel
    @2
    @5
    @26
    wb
    0re
    @22
    cc0
    cC
    leloe
    sylancr
    mpbid
    mpjaodan
end
