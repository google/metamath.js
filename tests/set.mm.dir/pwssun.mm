include "wss.mm"
include "wo.mm"
include "cun.mm"
include "cpw.mm"
include "wceq.mm"
include "ssequn2.mm"
include "pweq.mm"
include "eqimss.mm"
include "syl.mm"
include "sylbi.mm"
include "ssequn1.mm"
include "orim12i.mm"
include "orcoms.mm"
include "ssun.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "cpr.mm"
include "csn.mm"
include "vex.mm"
include "snss.mm"
include "unss12.mm"
include "syl2anb.mm"
include "zfpair2.mm"
include "elpw.mm"
include "df-pr.mm"
include "sseq1i.mm"
include "bitr2i.mm"
include "sylib.mm"
include "ssel.mm"
include "syl5.mm"
include "expcomd.mm"
include "imp31.mm"
include "elun.mm"
include "prss.mm"
include "bitr4i.mm"
include "simprbi.mm"
include "simplbi.mm"
include "ord.mm"
include "impancom.mm"
include "ssrdv.mm"
include "exp31.mm"
include "con1b.mm"
include "syl6ib.mm"
include "com23.mm"
include "imp.mm"
include "ex.mm"
include "orrd.mm"
include "impbii.mm"

theorem pwssun
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A C_ B \/ B C_ A ) <-> ~P ( A u. B ) C_ ( ~P A u. ~P B ) )

  proof
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wo
    #
    cA
    cB
    cun
    #
    cpw
    #
    cA
    cpw
    #
    cB
    cpw
    #
    cun
    #
    wss
    #
    @2
    @4
    @5
    wss
    #
    @4
    @6
    wss
    #
    wo
    #
    @8
    @1
    @0
    @11
    @1
    @9
    @0
    @10
    @1
    @3
    cA
    wceq
    #
    @9
    cB
    cA
    ssequn2
    @12
    @4
    @5
    wceq
    @9
    @3
    cA
    pweq
    @4
    @5
    eqimss
    syl
    sylbi
    @0
    @3
    cB
    wceq
    #
    @10
    cA
    cB
    ssequn1
    @13
    @4
    @6
    wceq
    @10
    @3
    cB
    pweq
    @4
    @6
    eqimss
    syl
    sylbi
    orim12i
    orcoms
    @4
    @5
    @6
    ssun
    syl
    @8
    @0
    @1
    @8
    @0
    wn
    #
    @1
    @8
    @14
    wa
    vy
    cB
    cA
    @8
    @14
    vy
    cv
    #
    cB
    wcel
    #
    @15
    cA
    wcel
    #
    wi
    @8
    @16
    @14
    @17
    @8
    @16
    @17
    wn
    #
    @0
    wi
    @14
    @17
    wi
    @8
    @16
    @18
    @0
    @8
    @16
    wa
    #
    @18
    wa
    vx
    cA
    cB
    @19
    vx
    cv
    #
    cA
    wcel
    #
    @18
    @20
    cB
    wcel
    #
    @19
    @21
    wa
    #
    @17
    @22
    @23
    @20
    @15
    cpr
    #
    @5
    wcel
    #
    @24
    @6
    wcel
    #
    wo
    #
    @17
    @22
    wo
    @23
    @24
    @7
    wcel
    #
    @27
    @8
    @16
    @21
    @28
    @8
    @21
    @16
    @28
    @21
    @16
    wa
    #
    @24
    @4
    wcel
    #
    @8
    @28
    @29
    @20
    csn
    #
    @15
    csn
    #
    cun
    #
    @3
    wss
    #
    @30
    @21
    @31
    cA
    wss
    @32
    cB
    wss
    @34
    @16
    @20
    cA
    vx
    vex
    #
    snss
    @15
    cB
    vy
    vex
    #
    snss
    @31
    cA
    @32
    cB
    unss12
    syl2anb
    @30
    @24
    @3
    wss
    @34
    @24
    @3
    vx
    vy
    zfpair2
    #
    elpw
    @24
    @33
    @3
    @20
    @15
    df-pr
    sseq1i
    bitr2i
    sylib
    @4
    @7
    @24
    ssel
    syl5
    expcomd
    imp31
    @24
    @5
    @6
    elun
    sylib
    @25
    @17
    @26
    @22
    @25
    @21
    @17
    @25
    @24
    cA
    wss
    @21
    @17
    wa
    @24
    cA
    @37
    elpw
    @20
    @15
    cA
    @35
    @36
    prss
    bitr4i
    simprbi
    @26
    @22
    @16
    @26
    @24
    cB
    wss
    @22
    @16
    wa
    @24
    cB
    @37
    elpw
    @20
    @15
    cB
    @35
    @36
    prss
    bitr4i
    simplbi
    orim12i
    syl
    ord
    impancom
    ssrdv
    exp31
    @17
    @0
    con1b
    syl6ib
    com23
    imp
    ssrdv
    ex
    orrd
    impbii
end
