include "cin.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "wa.mm"
include "cmd.mm"
include "wbr.mm"
include "cdmd.mm"
include "wb.mm"
include "ssin.mm"
include "chjcli.mm"
include "chlubi.mm"
include "anbi12i.mm"
include "cv.mm"
include "wi.mm"
include "cch.mm"
include "wral.mm"
include "wcel.mm"
include "chjcl.mm"
include "mpan2.mm"
include "wceq.mm"
include "sseq1.mm"
include "oveq1.mm"
include "ineq1d.mm"
include "sseq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "adantr.mm"
include "mdslmd1lem3.mm"
include "syld.mm"
include "ex.mm"
include "com3l.mm"
include "ralrimdv.mm"
include "mdbr2.mm"
include "mp2an.mm"
include "chincli.mm"
include "mdsl2i.mm"
include "3imtr4g.mm"
include "chincl.mm"
include "mdslmd1lem4.mm"
include "impbid.mm"
include "sylan2br.mm"

theorem mdslmd1i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  assume mdslmd.1: |- A e. CH
  assume mdslmd.2: |- B e. CH
  assume mdslmd.3: |- C e. CH
  assume mdslmd.4: |- D e. CH


  assert |- ( ( ( A MH B /\ B MH* A ) /\ ( A C_ ( C i^i D ) /\ ( C vH D ) C_ ( A vH B ) ) ) -> ( C MH D <-> ( C i^i B ) MH ( D i^i B ) ) )

  proof
    cA
    cC
    cD
    cin
    #
    wss
    #
    cC
    cD
    chj
    co
    cA
    cB
    chj
    co
    #
    wss
    #
    wa
    cA
    cB
    cmd
    wbr
    cB
    cA
    cdmd
    wbr
    wa
    #
    cA
    cC
    wss
    cA
    cD
    wss
    wa
    #
    cC
    @2
    wss
    cD
    @2
    wss
    wa
    #
    wa
    #
    cC
    cD
    cmd
    wbr
    #
    cC
    cB
    cin
    #
    cD
    cB
    cin
    #
    cmd
    wbr
    #
    wb
    @5
    @1
    @6
    @3
    cA
    cC
    cD
    ssin
    cC
    cD
    @2
    mdslmd.3
    mdslmd.4
    cA
    cB
    mdslmd.1
    mdslmd.2
    chjcli
    chlubi
    anbi12i
    @4
    @7
    wa
    #
    @8
    @11
    @12
    vy
    cv
    #
    cD
    wss
    #
    @13
    cC
    chj
    co
    #
    cD
    cin
    #
    @13
    @0
    chj
    co
    #
    wss
    #
    wi
    #
    vy
    cch
    wral
    #
    @9
    @10
    cin
    #
    vx
    cv
    #
    wss
    @22
    @10
    wss
    wa
    @22
    @9
    chj
    co
    @10
    cin
    @22
    @21
    chj
    co
    wss
    wi
    #
    vx
    cch
    wral
    @8
    @11
    @12
    @20
    @23
    vx
    cch
    @22
    cch
    wcel
    #
    @12
    @20
    @23
    @24
    @12
    @20
    @23
    wi
    @24
    @12
    wa
    #
    @20
    @22
    cA
    chj
    co
    #
    cD
    wss
    #
    @26
    cC
    chj
    co
    #
    cD
    cin
    #
    @26
    @0
    chj
    co
    #
    wss
    #
    wi
    #
    @23
    @24
    @20
    @32
    wi
    #
    @12
    @24
    @26
    cch
    wcel
    #
    @33
    @24
    cA
    cch
    wcel
    @34
    mdslmd.1
    @22
    cA
    chjcl
    mpan2
    @19
    @32
    vy
    @26
    cch
    @13
    @26
    wceq
    #
    @14
    @27
    @18
    @31
    @13
    @26
    cD
    sseq1
    @35
    @16
    @29
    @17
    @30
    @35
    @15
    @28
    cD
    @13
    @26
    cC
    chj
    oveq1
    ineq1d
    @13
    @26
    @0
    chj
    oveq1
    sseq12d
    imbi12d
    rspcv
    syl
    adantr
    vx
    cA
    cB
    cC
    cD
    mdslmd.1
    mdslmd.2
    mdslmd.3
    mdslmd.4
    mdslmd1lem3
    syld
    ex
    com3l
    ralrimdv
    cC
    cch
    wcel
    cD
    cch
    wcel
    @8
    @20
    wb
    mdslmd.3
    mdslmd.4
    vy
    cC
    cD
    mdbr2
    mp2an
    vx
    @9
    @10
    cC
    cB
    mdslmd.3
    mdslmd.2
    chincli
    #
    cD
    cB
    mdslmd.4
    mdslmd.2
    chincli
    #
    mdsl2i
    3imtr4g
    @12
    @13
    @10
    wss
    #
    @13
    @9
    chj
    co
    #
    @10
    cin
    #
    @13
    @21
    chj
    co
    #
    wss
    #
    wi
    #
    vy
    cch
    wral
    #
    @0
    @22
    wss
    @22
    cD
    wss
    wa
    @22
    cC
    chj
    co
    cD
    cin
    @22
    @0
    chj
    co
    wss
    wi
    #
    vx
    cch
    wral
    @11
    @8
    @12
    @44
    @45
    vx
    cch
    @24
    @12
    @44
    @45
    @24
    @12
    @44
    @45
    wi
    @25
    @44
    @22
    cB
    cin
    #
    @10
    wss
    #
    @46
    @9
    chj
    co
    #
    @10
    cin
    #
    @46
    @21
    chj
    co
    #
    wss
    #
    wi
    #
    @45
    @24
    @44
    @52
    wi
    #
    @12
    @24
    @46
    cch
    wcel
    #
    @53
    @24
    cB
    cch
    wcel
    @54
    mdslmd.2
    @22
    cB
    chincl
    mpan2
    @43
    @52
    vy
    @46
    cch
    @13
    @46
    wceq
    #
    @38
    @47
    @42
    @51
    @13
    @46
    @10
    sseq1
    @55
    @40
    @49
    @41
    @50
    @55
    @39
    @48
    @10
    @13
    @46
    @9
    chj
    oveq1
    ineq1d
    @13
    @46
    @21
    chj
    oveq1
    sseq12d
    imbi12d
    rspcv
    syl
    adantr
    vx
    cA
    cB
    cC
    cD
    mdslmd.1
    mdslmd.2
    mdslmd.3
    mdslmd.4
    mdslmd1lem4
    syld
    ex
    com3l
    ralrimdv
    @9
    cch
    wcel
    @10
    cch
    wcel
    @11
    @44
    wb
    @36
    @37
    vy
    @9
    @10
    mdbr2
    mp2an
    vx
    cC
    cD
    mdslmd.3
    mdslmd.4
    mdsl2i
    3imtr4g
    impbid
    sylan2br
end
