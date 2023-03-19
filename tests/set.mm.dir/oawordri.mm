include "con0.mm"
include "wcel.mm"
include "wss.mm"
include "coa.mm"
include "co.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "csuc.mm"
include "wa.mm"
include "wceq.mm"
include "oveq2.mm"
include "sseq12d.mm"
include "oa0.mm"
include "adantr.mm"
include "adantl.mm"
include "biimpar.mm"
include "wb.mm"
include "word.mm"
include "oacl.mm"
include "eloni.mm"
include "syl.mm"
include "ordsucsssuc.mm"
include "syl2an.mm"
include "anandirs.mm"
include "oasuc.mm"
include "adantlr.mm"
include "adantll.mm"
include "bitr4d.mm"
include "biimpd.mm"
include "expcom.mm"
include "adantrd.mm"
include "wlim.mm"
include "wral.mm"
include "cvv.mm"
include "vex.mm"
include "ciun.mm"
include "ss2iun.mm"
include "oalim.mm"
include "syl5ibr.mm"
include "mpanr1.mm"
include "tfinds3.mm"
include "exp4c.mm"
include "3imp231.mm"

theorem oawordri
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. On /\ B e. On /\ C e. On ) -> ( A C_ B -> ( A +o C ) C_ ( B +o C ) ) )

  proof
    cC
    con0
    wcel
    #
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cA
    cB
    wss
    #
    cA
    cC
    coa
    co
    #
    cB
    cC
    coa
    co
    #
    wss
    #
    wi
    @0
    @1
    @2
    @3
    @6
    cA
    vx
    cv
    #
    coa
    co
    #
    cB
    @7
    coa
    co
    #
    wss
    #
    cA
    c0
    coa
    co
    #
    cB
    c0
    coa
    co
    #
    wss
    #
    cA
    vy
    cv
    #
    coa
    co
    #
    cB
    @14
    coa
    co
    #
    wss
    #
    cA
    @14
    csuc
    #
    coa
    co
    #
    cB
    @18
    coa
    co
    #
    wss
    #
    @6
    @1
    @2
    wa
    #
    @3
    wa
    vx
    vy
    cC
    @7
    c0
    wceq
    @8
    @11
    @9
    @12
    @7
    c0
    cA
    coa
    oveq2
    @7
    c0
    cB
    coa
    oveq2
    sseq12d
    @7
    @14
    wceq
    @8
    @15
    @9
    @16
    @7
    @14
    cA
    coa
    oveq2
    @7
    @14
    cB
    coa
    oveq2
    sseq12d
    @7
    @18
    wceq
    @8
    @19
    @9
    @20
    @7
    @18
    cA
    coa
    oveq2
    @7
    @18
    cB
    coa
    oveq2
    sseq12d
    @7
    cC
    wceq
    @8
    @4
    @9
    @5
    @7
    cC
    cA
    coa
    oveq2
    @7
    cC
    cB
    coa
    oveq2
    sseq12d
    @22
    @13
    @3
    @22
    @11
    cA
    @12
    cB
    @1
    @11
    cA
    wceq
    @2
    cA
    oa0
    adantr
    @2
    @12
    cB
    wceq
    @1
    cB
    oa0
    adantl
    sseq12d
    biimpar
    @14
    con0
    wcel
    #
    @22
    @17
    @21
    wi
    #
    @3
    @22
    @23
    @24
    @22
    @23
    wa
    #
    @17
    @21
    @25
    @17
    @15
    csuc
    #
    @16
    csuc
    #
    wss
    #
    @21
    @1
    @2
    @23
    @17
    @28
    wb
    #
    @1
    @23
    wa
    #
    @15
    word
    #
    @16
    word
    #
    @29
    @2
    @23
    wa
    #
    @30
    @15
    con0
    wcel
    @31
    cA
    @14
    oacl
    @15
    eloni
    syl
    @33
    @16
    con0
    wcel
    @32
    cB
    @14
    oacl
    @16
    eloni
    syl
    @15
    @16
    ordsucsssuc
    syl2an
    anandirs
    @25
    @19
    @26
    @20
    @27
    @1
    @23
    @19
    @26
    wceq
    @2
    cA
    @14
    oasuc
    adantlr
    @2
    @23
    @20
    @27
    wceq
    @1
    cB
    @14
    oasuc
    adantll
    sseq12d
    bitr4d
    biimpd
    expcom
    adantrd
    @7
    wlim
    #
    @22
    @17
    vy
    @7
    wral
    #
    @10
    wi
    #
    @3
    @22
    @34
    @36
    @22
    @7
    cvv
    wcel
    #
    @34
    @36
    vx
    vex
    @35
    @10
    @22
    @37
    @34
    wa
    #
    wa
    #
    vy
    @7
    @15
    ciun
    #
    vy
    @7
    @16
    ciun
    #
    wss
    vy
    @7
    @15
    @16
    ss2iun
    @39
    @8
    @40
    @9
    @41
    @1
    @38
    @8
    @40
    wceq
    @2
    vy
    cA
    @7
    cvv
    oalim
    adantlr
    @2
    @38
    @9
    @41
    wceq
    @1
    vy
    cB
    @7
    cvv
    oalim
    adantll
    sseq12d
    syl5ibr
    mpanr1
    expcom
    adantrd
    tfinds3
    exp4c
    3imp231
end
