include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "cmul.mm"
include "co.mm"
include "wb.mm"
include "rereb.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "recl.mm"
include "recnd.mm"
include "simp1.mm"
include "recn.mm"
include "anim1i.mm"
include "3adant1.mm"
include "mulcan.mm"
include "syl3anc.mm"
include "ci.mm"
include "cim.mm"
include "caddc.mm"
include "adantr.mm"
include "adantl.mm"
include "ax-icn.mm"
include "imcl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "adddid.mm"
include "replim.mm"
include "oveq2d.mm"
include "mul12.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "3eqtr4d.mm"
include "fveq2d.mm"
include "remulcl.mm"
include "sylan2.mm"
include "crre.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "eqeq1d.mm"
include "sylan.mm"
include "syl.mm"
include "bitr4d.mm"
include "ancoms.mm"
include "3adant3.mm"
include "3bitr2d.mm"

theorem mulre
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. RR /\ B =/= 0 ) -> ( A e. RR <-> ( B x. A ) e. RR ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cr
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cA
    cr
    wcel
    #
    cA
    cre
    cfv
    #
    cA
    wceq
    #
    cB
    @5
    cmul
    co
    #
    cB
    cA
    cmul
    co
    #
    wceq
    #
    @8
    cr
    wcel
    #
    @0
    @1
    @4
    @6
    wb
    @2
    cA
    rereb
    3ad2ant1
    @3
    @5
    cc
    wcel
    #
    @0
    cB
    cc
    wcel
    #
    @2
    wa
    #
    @9
    @6
    wb
    @0
    @1
    @11
    @2
    @0
    @5
    cA
    recl
    #
    recnd
    #
    3ad2ant1
    @0
    @1
    @2
    simp1
    @1
    @2
    @13
    @0
    @1
    @12
    @2
    cB
    recn
    #
    anim1i
    3adant1
    @5
    cA
    cB
    mulcan
    syl3anc
    @0
    @1
    @9
    @10
    wb
    #
    @2
    @1
    @0
    @17
    @1
    @0
    wa
    #
    @9
    @8
    cre
    cfv
    #
    @8
    wceq
    #
    @10
    @18
    @7
    @19
    @8
    @18
    @19
    @7
    ci
    cB
    cA
    cim
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cre
    cfv
    #
    @7
    @18
    @8
    @24
    cre
    @18
    cB
    @5
    ci
    @21
    cmul
    co
    #
    caddc
    co
    #
    cmul
    co
    @7
    cB
    @26
    cmul
    co
    #
    caddc
    co
    @8
    @24
    @18
    cB
    @5
    @26
    @1
    @12
    @0
    @16
    adantr
    @0
    @11
    @1
    @15
    adantl
    @0
    @26
    cc
    wcel
    #
    @1
    @0
    ci
    cc
    wcel
    #
    @21
    cc
    wcel
    #
    @29
    ax-icn
    @0
    @21
    cA
    imcl
    #
    recnd
    #
    ci
    @21
    mulcl
    sylancr
    adantl
    adddid
    @18
    cA
    @27
    cB
    cmul
    @0
    cA
    @27
    wceq
    @1
    cA
    replim
    adantl
    oveq2d
    @18
    @23
    @28
    @7
    caddc
    @1
    @12
    @31
    @23
    @28
    wceq
    #
    @0
    @16
    @33
    @30
    @12
    @31
    @34
    ax-icn
    ci
    cB
    @21
    mul12
    mp3an1
    syl2an
    oveq2d
    3eqtr4d
    fveq2d
    @18
    @7
    cr
    wcel
    #
    @22
    cr
    wcel
    #
    @25
    @7
    wceq
    @0
    @1
    @5
    cr
    wcel
    @35
    @14
    cB
    @5
    remulcl
    sylan2
    @0
    @1
    @21
    cr
    wcel
    @36
    @32
    cB
    @21
    remulcl
    sylan2
    @7
    @22
    crre
    syl2anc
    eqtr2d
    eqeq1d
    @18
    @8
    cc
    wcel
    #
    @10
    @20
    wb
    @1
    @12
    @0
    @37
    @16
    cB
    cA
    mulcl
    sylan
    @8
    rereb
    syl
    bitr4d
    ancoms
    3adant3
    3bitr2d
end
