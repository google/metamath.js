include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "comu.mm"
include "co.mm"
include "coa.mm"
include "wceq.mm"
include "w3o.mm"
include "word.mm"
include "simpl2l.mm"
include "eloni.mm"
include "syl.mm"
include "simpl3l.mm"
include "ordtri3or.mm"
include "syl2anc.mm"
include "simpr.mm"
include "wn.mm"
include "simpl1l.mm"
include "omcl.mm"
include "simpl3r.mm"
include "onelon.mm"
include "oacl.mm"
include "ordirr.mm"
include "3syl.mm"
include "eqneltrd.mm"
include "wo.mm"
include "orc.mm"
include "wi.mm"
include "omeulem2.mm"
include "adantr.mm"
include "syl5.mm"
include "mtod.mm"
include "pm2.21d.mm"
include "idd.mm"
include "neleqtrrd.mm"
include "simpl1r.mm"
include "simpl2r.mm"
include "syl222anc.mm"
include "3jaod.mm"
include "mpd.mm"
include "olc.mm"
include "mpand.mm"
include "eqcomd.mm"
include "jca.mm"
include "ex.mm"
include "oveq2.mm"
include "id.mm"
include "oveqan12d.mm"
include "impbid1.mm"

theorem omopth2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E


  assert |- ( ( ( A e. On /\ A =/= (/) ) /\ ( B e. On /\ C e. A ) /\ ( D e. On /\ E e. A ) ) -> ( ( ( A .o B ) +o C ) = ( ( A .o D ) +o E ) <-> ( B = D /\ C = E ) ) )

  proof
    cA
    con0
    wcel
    #
    cA
    c0
    wne
    #
    wa
    #
    cB
    con0
    wcel
    #
    cC
    cA
    wcel
    #
    wa
    #
    cD
    con0
    wcel
    #
    cE
    cA
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cB
    comu
    co
    #
    cC
    coa
    co
    #
    cA
    cD
    comu
    co
    #
    cE
    coa
    co
    #
    wceq
    #
    cB
    cD
    wceq
    #
    cC
    cE
    wceq
    #
    wa
    #
    @9
    @14
    @17
    @9
    @14
    wa
    #
    @15
    @16
    @18
    cB
    cD
    wcel
    #
    @15
    cD
    cB
    wcel
    #
    w3o
    #
    @15
    @18
    cB
    word
    #
    cD
    word
    #
    @21
    @18
    @3
    @22
    @3
    @4
    @2
    @8
    @14
    simpl2l
    #
    cB
    eloni
    syl
    @18
    @6
    @23
    @6
    @7
    @2
    @5
    @14
    simpl3l
    #
    cD
    eloni
    syl
    cB
    cD
    ordtri3or
    syl2anc
    @18
    @19
    @15
    @15
    @20
    @18
    @19
    @15
    @18
    @19
    @11
    @13
    wcel
    #
    @18
    @11
    @13
    @13
    @9
    @14
    simpr
    #
    @18
    @13
    con0
    wcel
    #
    @13
    word
    @13
    @13
    wcel
    wn
    @18
    @12
    con0
    wcel
    #
    cE
    con0
    wcel
    #
    @28
    @18
    @0
    @6
    @29
    @0
    @1
    @5
    @8
    @14
    simpl1l
    #
    @25
    cA
    cD
    omcl
    syl2anc
    @18
    @0
    @7
    @30
    @31
    @6
    @7
    @2
    @5
    @14
    simpl3r
    #
    cA
    cE
    onelon
    #
    syl2anc
    @12
    cE
    oacl
    syl2anc
    @13
    eloni
    @13
    ordirr
    3syl
    #
    eqneltrd
    #
    @19
    @19
    @15
    cC
    cE
    wcel
    #
    wa
    #
    wo
    #
    @18
    @26
    @19
    @37
    orc
    @9
    @38
    @26
    wi
    @14
    cA
    cB
    cC
    cD
    cE
    omeulem2
    adantr
    #
    syl5
    mtod
    pm2.21d
    @18
    @15
    idd
    @18
    @20
    @15
    @18
    @20
    @13
    @11
    wcel
    #
    @18
    @11
    @13
    @13
    @34
    @27
    neleqtrrd
    #
    @20
    @20
    cD
    cB
    wceq
    #
    cE
    cC
    wcel
    #
    wa
    #
    wo
    #
    @18
    @40
    @20
    @44
    orc
    @18
    @0
    @1
    @6
    @7
    @3
    @4
    @45
    @40
    wi
    @31
    @0
    @1
    @5
    @8
    @14
    simpl1r
    @25
    @32
    @24
    @3
    @4
    @2
    @8
    @14
    simpl2r
    #
    cA
    cD
    cE
    cB
    cC
    omeulem2
    syl222anc
    #
    syl5
    mtod
    pm2.21d
    3jaod
    mpd
    #
    @18
    @36
    @16
    @43
    w3o
    #
    @16
    @18
    cC
    word
    #
    cE
    word
    #
    @49
    @18
    @0
    @4
    @50
    @31
    @46
    @0
    @4
    wa
    cC
    con0
    wcel
    @50
    cA
    cC
    onelon
    cC
    eloni
    syl
    syl2anc
    @18
    @0
    @7
    @51
    @31
    @32
    @0
    @7
    wa
    @30
    @51
    @33
    cE
    eloni
    syl
    syl2anc
    cC
    cE
    ordtri3or
    syl2anc
    @18
    @36
    @16
    @16
    @43
    @18
    @36
    @16
    @18
    @36
    @26
    @35
    @18
    @15
    @36
    @26
    @48
    @37
    @38
    @18
    @26
    @37
    @19
    olc
    @39
    syl5
    mpand
    mtod
    pm2.21d
    @18
    @16
    idd
    @18
    @43
    @16
    @18
    @43
    @40
    @41
    @18
    @42
    @43
    @40
    @18
    cB
    cD
    @48
    eqcomd
    @44
    @45
    @18
    @40
    @44
    @20
    olc
    @47
    syl5
    mpand
    mtod
    pm2.21d
    3jaod
    mpd
    jca
    ex
    @15
    @16
    @10
    @12
    cC
    cE
    coa
    cB
    cD
    cA
    comu
    oveq2
    @16
    id
    oveqan12d
    impbid1
end
