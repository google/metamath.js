include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cmnf.mm"
include "wne.mm"
include "wa.mm"
include "cr.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "wb.mm"
include "cpnf.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "xnegcl.mm"
include "syl.mm"
include "xaddcl.mm"
include "syl2anc.mm"
include "adantr.mm"
include "simpll3.mm"
include "simpr.mm"
include "xleadd1.mm"
include "syl3anc.mm"
include "xnpcan.mm"
include "sylan.mm"
include "breq1d.mm"
include "bitrd.mm"
include "simpr3.mm"
include "oveq1.mm"
include "pnfaddmnf.mm"
include "syl6eq.mm"
include "syl5ibrcom.mm"
include "wi.mm"
include "xaddmnf1.mm"
include "ex.mm"
include "simpl3.mm"
include "mnfle.mm"
include "breq1.mm"
include "syld.mm"
include "pm2.61dne.mm"
include "pnfge.mm"
include "ge0nemnf.mm"
include "xaddpnf1.mm"
include "breqtrrd.mm"
include "2thd.mm"
include "xnegeq.mm"
include "xnegpnf.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "breq2d.mm"
include "bibi12d.mm"
include "imp.mm"
include "wo.mm"
include "simpr2.mm"
include "jca.mm"
include "xrnemnf.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem xlesubadd
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ ( 0 <_ A /\ B =/= -oo /\ 0 <_ C ) ) -> ( ( A +e -e B ) <_ C <-> A <_ ( C +e B ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cc0
    cA
    cle
    wbr
    #
    cB
    cmnf
    wne
    #
    cc0
    cC
    cle
    wbr
    #
    w3a
    #
    wa
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cxne
    #
    cxad
    co
    #
    cC
    cle
    wbr
    #
    cA
    cC
    cB
    cxad
    co
    #
    cle
    wbr
    #
    wb
    #
    cB
    cpnf
    wceq
    #
    @8
    @9
    wa
    #
    @12
    @11
    cB
    cxad
    co
    #
    @13
    cle
    wbr
    #
    @14
    @17
    @11
    cxr
    wcel
    #
    @2
    @9
    @12
    @19
    wb
    @8
    @20
    @9
    @8
    @0
    @10
    cxr
    wcel
    #
    @20
    @0
    @1
    @2
    @7
    simpl1
    #
    @8
    @1
    @21
    @0
    @1
    @2
    @7
    simpl2
    #
    cB
    xnegcl
    syl
    cA
    @10
    xaddcl
    syl2anc
    adantr
    @0
    @1
    @2
    @7
    @9
    simpll3
    @8
    @9
    simpr
    @11
    cC
    cB
    xleadd1
    syl3anc
    @17
    @18
    cA
    @13
    cle
    @8
    @0
    @9
    @18
    cA
    wceq
    @22
    cA
    cB
    xnpcan
    sylan
    breq1d
    bitrd
    @8
    @16
    @15
    @8
    @15
    @16
    cA
    cmnf
    cxad
    co
    #
    cC
    cle
    wbr
    #
    cA
    cC
    cpnf
    cxad
    co
    #
    cle
    wbr
    #
    wb
    @8
    @25
    @27
    @8
    @25
    cA
    cpnf
    @8
    @25
    cA
    cpnf
    wceq
    #
    @6
    @3
    @4
    @5
    @6
    simpr3
    #
    @28
    @24
    cc0
    cC
    cle
    @28
    @24
    cpnf
    cmnf
    cxad
    co
    cc0
    cA
    cpnf
    cmnf
    cxad
    oveq1
    pnfaddmnf
    syl6eq
    breq1d
    syl5ibrcom
    @8
    cA
    cpnf
    wne
    #
    @24
    cmnf
    wceq
    #
    @25
    @8
    @0
    @30
    @31
    wi
    @22
    @0
    @30
    @31
    cA
    xaddmnf1
    ex
    syl
    @8
    @25
    @31
    cmnf
    cC
    cle
    wbr
    #
    @8
    @2
    @32
    @0
    @1
    @2
    @7
    simpl3
    #
    cC
    mnfle
    syl
    @24
    cmnf
    cC
    cle
    breq1
    syl5ibrcom
    syld
    pm2.61dne
    @8
    cA
    cpnf
    @26
    cle
    @8
    @0
    cA
    cpnf
    cle
    wbr
    @22
    cA
    pnfge
    syl
    @8
    @2
    cC
    cmnf
    wne
    #
    @26
    cpnf
    wceq
    @33
    @8
    @2
    @6
    @34
    @33
    @29
    cC
    ge0nemnf
    syl2anc
    cC
    xaddpnf1
    syl2anc
    breqtrrd
    2thd
    @16
    @12
    @25
    @14
    @27
    @16
    @11
    @24
    cC
    cle
    @16
    @10
    cmnf
    cA
    cxad
    @16
    @10
    cpnf
    cxne
    cmnf
    cB
    cpnf
    xnegeq
    xnegpnf
    syl6eq
    oveq2d
    breq1d
    @16
    @13
    @26
    cA
    cle
    cB
    cpnf
    cC
    cxad
    oveq2
    breq2d
    bibi12d
    syl5ibrcom
    imp
    @8
    @1
    @5
    wa
    @9
    @16
    wo
    @8
    @1
    @5
    @23
    @3
    @4
    @5
    @6
    simpr2
    jca
    cB
    xrnemnf
    sylib
    mpjaodan
end
