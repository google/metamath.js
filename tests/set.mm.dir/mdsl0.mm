include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "cmd.mm"
include "wbr.mm"
include "cv.mm"
include "chj.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "sstr2.mm"
include "com12.mm"
include "ad2antlr.mm"
include "w3a.mm"
include "chlej2.mm"
include "ss2in.mm"
include "ex.mm"
include "syl.mm"
include "3expia.mm"
include "ancoms.mm"
include "ad2ant2r.mm"
include "imp43.mm"
include "adantrr.mm"
include "oveq2.mm"
include "chj0.mm"
include "sylan9eqr.mm"
include "adantl.mm"
include "chincl.mm"
include "chub1.mm"
include "sylan.mm"
include "eqsstrd.mm"
include "adantll.mm"
include "anassrs.mm"
include "adantrl.mm"
include "syl6.mm"
include "com23.mm"
include "sylc.mm"
include "an32s.mm"
include "imim12d.mm"
include "ralimdva.mm"
include "wb.mm"
include "mdbr2.mm"
include "ad2antrr.mm"
include "3imtr4d.mm"
include "expimpd.mm"

theorem mdsl0
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x


  assert |- ( ( ( A e. CH /\ B e. CH ) /\ ( C e. CH /\ D e. CH ) ) -> ( ( ( ( C C_ A /\ D C_ B ) /\ ( A i^i B ) = 0H ) /\ A MH B ) -> C MH D ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    #
    cC
    cch
    wcel
    #
    cD
    cch
    wcel
    #
    wa
    #
    wa
    #
    cC
    cA
    wss
    #
    cD
    cB
    wss
    #
    wa
    #
    cA
    cB
    cin
    #
    c0h
    wceq
    #
    wa
    #
    cA
    cB
    cmd
    wbr
    #
    cC
    cD
    cmd
    wbr
    #
    @6
    @12
    wa
    #
    vx
    cv
    #
    cB
    wss
    #
    @16
    cA
    chj
    co
    #
    cB
    cin
    #
    @16
    @10
    chj
    co
    #
    wss
    #
    wi
    #
    vx
    cch
    wral
    #
    @16
    cD
    wss
    #
    @16
    cC
    chj
    co
    #
    cD
    cin
    #
    @16
    cC
    cD
    cin
    #
    chj
    co
    #
    wss
    #
    wi
    #
    vx
    cch
    wral
    #
    @13
    @14
    @15
    @22
    @30
    vx
    cch
    @15
    @16
    cch
    wcel
    #
    wa
    @24
    @17
    @21
    @29
    @12
    @24
    @17
    wi
    #
    @6
    @32
    @8
    @33
    @7
    @11
    @24
    @8
    @17
    @16
    cD
    cB
    sstr2
    com12
    ad2antlr
    ad2antlr
    @6
    @32
    @12
    @21
    @29
    wi
    #
    @6
    @32
    wa
    #
    @12
    wa
    @26
    @19
    wss
    #
    @20
    @28
    wss
    #
    @34
    @35
    @9
    @36
    @11
    @6
    @32
    @7
    @8
    @36
    @0
    @3
    @32
    @7
    @8
    @36
    wi
    #
    wi
    #
    wi
    #
    @1
    @4
    @3
    @0
    @40
    @3
    @0
    @32
    @39
    @3
    @0
    @32
    w3a
    #
    @7
    @38
    @41
    @7
    wa
    @25
    @18
    wss
    #
    @38
    cC
    cA
    @16
    chlej2
    @42
    @8
    @36
    @25
    @18
    cD
    cB
    ss2in
    ex
    syl
    ex
    3expia
    ancoms
    ad2ant2r
    imp43
    adantrr
    @35
    @11
    @37
    @9
    @6
    @32
    @11
    @37
    @5
    @32
    @11
    wa
    #
    @37
    @2
    @5
    @43
    wa
    @20
    @16
    @28
    @43
    @20
    @16
    wceq
    @5
    @11
    @32
    @20
    @16
    c0h
    chj
    co
    @16
    @10
    c0h
    @16
    chj
    oveq2
    @16
    chj0
    sylan9eqr
    adantl
    @5
    @32
    @16
    @28
    wss
    #
    @11
    @5
    @27
    cch
    wcel
    #
    @32
    @44
    cC
    cD
    chincl
    @32
    @45
    @44
    @16
    @27
    chub1
    ancoms
    sylan
    adantrr
    eqsstrd
    adantll
    anassrs
    adantrl
    @36
    @21
    @37
    @29
    @36
    @21
    @26
    @20
    wss
    @37
    @29
    wi
    @26
    @19
    @20
    sstr2
    @26
    @20
    @28
    sstr2
    syl6
    com23
    sylc
    an32s
    imim12d
    ralimdva
    @2
    @13
    @23
    wb
    @5
    @12
    vx
    cA
    cB
    mdbr2
    ad2antrr
    @5
    @14
    @31
    wb
    @2
    @12
    vx
    cC
    cD
    mdbr2
    ad2antlr
    3imtr4d
    expimpd
end
