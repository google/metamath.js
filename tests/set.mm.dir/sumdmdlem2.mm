include "cv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wss.mm"
include "cat.mm"
include "wral.mm"
include "cph.mm"
include "wa.mm"
include "wceq.mm"
include "wcel.mm"
include "chil.mm"
include "wi.mm"
include "chjcli.mm"
include "cheli.mm"
include "wn.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "csh.mm"
include "spansnsh.mm"
include "chshii.mm"
include "shsub2.mm"
include "sylancl.mm"
include "spansnid.mm"
include "sseldd.mm"
include "ad2antrl.mm"
include "elin.mm"
include "c0v.mm"
include "wne.mm"
include "df-ne.mm"
include "spansna.mm"
include "sylan2br.mm"
include "oveq1.mm"
include "ineq1d.mm"
include "oveq1d.mm"
include "sseq12d.mm"
include "rspcv.mm"
include "syl.mm"
include "wb.mm"
include "cch.mm"
include "spansnj.mm"
include "spansnch.mm"
include "chjcom.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "mpan.mm"
include "adantr.mm"
include "sylibrd.mm"
include "com12.mm"
include "expdimp.mm"
include "ssid.mm"
include "c0h.mm"
include "sneq.mm"
include "fveq2d.mm"
include "spansn0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "shs0i.mm"
include "inss1.mm"
include "chub2i.mm"
include "ssini.mm"
include "eqssi.mm"
include "chincli.mm"
include "chjcomi.mm"
include "chabs1i.mm"
include "eqtri.mm"
include "mpbiri.mm"
include "pm2.61d2.mm"
include "adantrr.mm"
include "sumdmdlem.mm"
include "shsub2i.mm"
include "syl6eqss.mm"
include "adantl.mm"
include "sstrd.mm"
include "sseld.mm"
include "syl5bir.mm"
include "mpand.mm"
include "exp32.mm"
include "com34.mm"
include "pm2.18.mm"
include "syl8.mm"
include "syl5.mm"
include "pm2.43d.mm"
include "ssrdv.mm"
include "chsleji.mm"
include "jctil.mm"
include "eqss.mm"
include "sylibr.mm"

theorem sumdmdlem2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  assume sumdmdi.1: |- A e. CH
  assume sumdmdi.2: |- B e. CH

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint C y
  disjoint C z
  disjoint C w
  assert |- ( A. x e. HAtoms ( ( x vH B ) i^i ( A vH B ) ) C_ ( ( ( x vH B ) i^i A ) vH B ) -> ( A +H B ) = ( A vH B ) )

  proof
    vx
    cv
    #
    cB
    chj
    co
    #
    cA
    cB
    chj
    co
    #
    cin
    #
    @1
    cA
    cin
    #
    cB
    chj
    co
    #
    wss
    #
    vx
    cat
    wral
    #
    cA
    cB
    cph
    co
    #
    @2
    wss
    #
    @2
    @8
    wss
    #
    wa
    @8
    @2
    wceq
    @7
    @10
    @9
    @7
    vy
    @2
    @8
    @7
    vy
    cv
    #
    @2
    wcel
    #
    @11
    @8
    wcel
    #
    @12
    @11
    chil
    wcel
    #
    @7
    @12
    @13
    wi
    #
    @11
    @2
    cA
    cB
    sumdmdi.1
    sumdmdi.2
    chjcli
    cheli
    @7
    @14
    @12
    @13
    wn
    #
    @13
    wi
    @13
    @7
    @14
    @16
    @12
    @13
    @7
    @14
    @16
    @15
    @7
    @14
    @16
    wa
    #
    wa
    #
    @11
    cB
    @11
    csn
    #
    cspn
    cfv
    #
    cph
    co
    #
    wcel
    #
    @12
    @13
    @14
    @22
    @7
    @16
    @14
    @20
    @21
    @11
    @14
    @20
    csh
    wcel
    cB
    csh
    wcel
    @20
    @21
    wss
    @11
    spansnsh
    cB
    sumdmdi.2
    chshii
    #
    @20
    cB
    shsub2
    sylancl
    @11
    spansnid
    sseldd
    ad2antrl
    @22
    @12
    wa
    @11
    @21
    @2
    cin
    #
    wcel
    @18
    @13
    @11
    @21
    @2
    elin
    @18
    @24
    @8
    @11
    @18
    @24
    @21
    cA
    cin
    #
    cB
    chj
    co
    #
    @8
    @7
    @14
    @24
    @26
    wss
    #
    @16
    @7
    @14
    wa
    @11
    c0v
    wceq
    #
    @27
    @7
    @14
    @28
    wn
    #
    @27
    @14
    @29
    wa
    #
    @7
    @27
    @30
    @7
    @20
    cB
    chj
    co
    #
    @2
    cin
    #
    @31
    cA
    cin
    #
    cB
    chj
    co
    #
    wss
    #
    @27
    @30
    @20
    cat
    wcel
    #
    @7
    @35
    wi
    @29
    @14
    @11
    c0v
    wne
    @36
    @11
    c0v
    df-ne
    @11
    spansna
    sylan2br
    @6
    @35
    vx
    @20
    cat
    @0
    @20
    wceq
    #
    @3
    @32
    @5
    @34
    @37
    @1
    @31
    @2
    @0
    @20
    cB
    chj
    oveq1
    #
    ineq1d
    @37
    @4
    @33
    cB
    chj
    @37
    @1
    @31
    cA
    @38
    ineq1d
    oveq1d
    sseq12d
    rspcv
    syl
    @14
    @27
    @35
    wb
    @29
    @14
    @24
    @32
    @26
    @34
    @14
    @21
    @31
    @2
    cB
    cch
    wcel
    #
    @14
    @21
    @31
    wceq
    sumdmdi.2
    @39
    @14
    wa
    @21
    cB
    @20
    chj
    co
    #
    @31
    cB
    @11
    spansnj
    @14
    @39
    @20
    cch
    wcel
    @40
    @31
    wceq
    @11
    spansnch
    cB
    @20
    chjcom
    sylan2
    eqtrd
    mpan
    #
    ineq1d
    @14
    @25
    @33
    cB
    chj
    @14
    @21
    @31
    cA
    @41
    ineq1d
    oveq1d
    sseq12d
    adantr
    sylibrd
    com12
    expdimp
    @28
    @27
    cB
    cB
    wss
    cB
    ssid
    #
    @28
    @24
    cB
    @26
    cB
    @28
    @24
    cB
    @2
    cin
    #
    cB
    @28
    @21
    cB
    @2
    @28
    @21
    cB
    c0h
    cph
    co
    cB
    @28
    @20
    c0h
    cB
    cph
    @28
    @20
    c0v
    csn
    #
    cspn
    cfv
    c0h
    @28
    @19
    @44
    cspn
    @11
    c0v
    sneq
    fveq2d
    spansn0
    syl6eq
    oveq2d
    cB
    @23
    shs0i
    syl6eq
    #
    ineq1d
    @43
    cB
    cB
    @2
    inss1
    cB
    cB
    @2
    @42
    cB
    cA
    sumdmdi.2
    sumdmdi.1
    chub2i
    ssini
    eqssi
    syl6eq
    @28
    @26
    cB
    cA
    cin
    #
    cB
    chj
    co
    #
    cB
    @28
    @25
    @46
    cB
    chj
    @28
    @21
    cB
    cA
    @45
    ineq1d
    oveq1d
    @47
    cB
    @46
    chj
    co
    cB
    @46
    cB
    cB
    cA
    sumdmdi.2
    sumdmdi.1
    chincli
    sumdmdi.2
    chjcomi
    cB
    cA
    sumdmdi.2
    sumdmdi.1
    chabs1i
    eqtri
    #
    syl6eq
    sseq12d
    mpbiri
    pm2.61d2
    adantrr
    @17
    @26
    @8
    wss
    @7
    @17
    @26
    cB
    @8
    @17
    @26
    @47
    cB
    @17
    @25
    @46
    cB
    chj
    cA
    cB
    @11
    sumdmdi.1
    sumdmdi.2
    sumdmdlem
    oveq1d
    @48
    syl6eq
    cB
    cA
    @23
    cA
    sumdmdi.1
    chshii
    shsub2i
    syl6eqss
    adantl
    sstrd
    sseld
    syl5bir
    mpand
    exp32
    com34
    @13
    pm2.18
    syl8
    syl5
    pm2.43d
    ssrdv
    cA
    cB
    sumdmdi.1
    sumdmdi.2
    chsleji
    jctil
    @8
    @2
    eqss
    sylibr
end
