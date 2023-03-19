include "cmd.mm"
include "wbr.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wss.mm"
include "w3a.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "cch.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "chjass.mm"
include "mp3an12.mm"
include "chjcli.mm"
include "chjcom.mm"
include "mpan2.mm"
include "chjcl.mm"
include "mpan.mm"
include "sylancl.mm"
include "3eqtr4d.mm"
include "ineq1d.mm"
include "inass.mm"
include "incom.mm"
include "chjcomi.mm"
include "ineq2i.mm"
include "chabs2i.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "ad2antrr.mm"
include "chlej2.mm"
include "ex.mm"
include "mp3an23.mm"
include "mdi.mm"
include "exp32.mm"
include "syl.mm"
include "com23.mm"
include "syld.mm"
include "imp31.mm"
include "adantrr.mm"
include "chincli.mm"
include "imp.mm"
include "chjidmi.mm"
include "oveq1i.mm"
include "3eqtr3a.mm"
include "eqtrd.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "ad2ant2rl.mm"
include "eqsstrd.mm"
include "ssrin.mm"
include "adantrl.mm"
include "chub2i.mm"
include "ax-mp.mm"
include "mpi.mm"
include "sstrd.mm"
include "exp31.mm"
include "com3r.mm"
include "3impb.mm"
include "ralrimiv.mm"
include "wb.mm"
include "mdbr2.mm"
include "mp2an.mm"
include "sylibr.mm"
include "3eqtr3ri.mm"
include "ineq12i.mm"
include "chub1i.mm"
include "mp3an.mm"
include "chlejb1i.mm"
include "biimpi.mm"
include "syl5eq.mm"
include "sylan9eq.mm"
include "syl5eqr.mm"
include "3adant1.mm"
include "jca.mm"

theorem mdexchi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  assume mdexch.1: |- A e. CH
  assume mdexch.2: |- B e. CH
  assume mdexch.3: |- C e. CH


  assert |- ( ( A MH B /\ C MH ( A vH B ) /\ ( C i^i ( A vH B ) ) C_ A ) -> ( ( C vH A ) MH B /\ ( ( C vH A ) i^i B ) = ( A i^i B ) ) )

  proof
    cA
    cB
    cmd
    wbr
    #
    cC
    cA
    cB
    chj
    co
    #
    cmd
    wbr
    #
    cC
    @1
    cin
    #
    cA
    wss
    #
    w3a
    #
    cC
    cA
    chj
    co
    #
    cB
    cmd
    wbr
    #
    @6
    cB
    cin
    #
    cA
    cB
    cin
    #
    wceq
    #
    @5
    vx
    cv
    #
    cB
    wss
    #
    @11
    @6
    chj
    co
    #
    cB
    cin
    #
    @11
    @8
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
    @7
    @5
    @17
    vx
    cch
    @0
    @2
    @4
    @11
    cch
    wcel
    #
    @17
    wi
    @19
    @12
    @0
    @2
    @4
    wa
    #
    wa
    #
    @16
    @19
    @12
    @21
    @16
    @19
    @12
    wa
    #
    @21
    wa
    @14
    @11
    cA
    chj
    co
    #
    cB
    cin
    #
    @15
    @22
    @20
    @14
    @24
    wss
    @0
    @22
    @20
    wa
    #
    @14
    cA
    @11
    chj
    co
    #
    cC
    chj
    co
    #
    @1
    cin
    #
    cB
    cin
    #
    @24
    @19
    @14
    @29
    wceq
    @12
    @20
    @19
    @14
    @27
    cB
    cin
    #
    @29
    @19
    @13
    @27
    cB
    @19
    @6
    @11
    chj
    co
    #
    cC
    @26
    chj
    co
    #
    @13
    @27
    cC
    cch
    wcel
    #
    cA
    cch
    wcel
    #
    @19
    @31
    @32
    wceq
    mdexch.3
    mdexch.1
    cC
    cA
    @11
    chjass
    mp3an12
    @19
    @6
    cch
    wcel
    #
    @13
    @31
    wceq
    cC
    cA
    mdexch.3
    mdexch.1
    chjcli
    #
    @11
    @6
    chjcom
    mpan2
    @19
    @26
    cch
    wcel
    #
    @33
    @27
    @32
    wceq
    @34
    @19
    @37
    mdexch.1
    cA
    @11
    chjcl
    mpan
    #
    mdexch.3
    @26
    cC
    chjcom
    sylancl
    3eqtr4d
    ineq1d
    @29
    @27
    @1
    cB
    cin
    #
    cin
    @30
    @27
    @1
    cB
    inass
    @39
    cB
    @27
    @39
    cB
    @1
    cin
    #
    cB
    @1
    cB
    incom
    @40
    cB
    cB
    cA
    chj
    co
    #
    cin
    #
    cB
    @1
    @41
    cB
    cA
    cB
    mdexch.1
    mdexch.2
    chjcomi
    ineq2i
    #
    cB
    cA
    mdexch.2
    mdexch.1
    chabs2i
    #
    eqtri
    eqtri
    ineq2i
    eqtri
    syl6eqr
    ad2antrr
    @25
    @28
    @23
    wss
    @29
    @24
    wss
    @25
    @28
    @26
    @3
    chj
    co
    #
    @23
    @22
    @2
    @28
    @45
    wceq
    #
    @4
    @19
    @12
    @2
    @46
    @19
    @12
    @26
    @1
    wss
    #
    @2
    @46
    wi
    @19
    cB
    cch
    wcel
    #
    @34
    @12
    @47
    wi
    mdexch.2
    mdexch.1
    @19
    @48
    @34
    w3a
    @12
    @47
    @11
    cB
    cA
    chlej2
    ex
    mp3an23
    @19
    @2
    @47
    @46
    @19
    @37
    @2
    @47
    @46
    wi
    wi
    #
    @38
    @33
    @1
    cch
    wcel
    #
    @37
    @49
    mdexch.3
    cA
    cB
    mdexch.1
    mdexch.2
    chjcli
    #
    @33
    @50
    @37
    w3a
    @2
    @47
    @46
    cC
    @1
    @26
    mdi
    exp32
    mp3an12
    syl
    com23
    syld
    imp31
    adantrr
    @19
    @4
    @45
    @23
    wss
    @12
    @2
    @19
    @4
    wa
    @45
    @26
    cA
    chj
    co
    #
    @23
    @19
    @4
    @45
    @52
    wss
    #
    @19
    @37
    @4
    @53
    wi
    #
    @38
    @3
    cch
    wcel
    #
    @34
    @37
    @54
    cC
    @1
    mdexch.3
    @51
    chincli
    #
    mdexch.1
    @55
    @34
    @37
    w3a
    @4
    @53
    @3
    cA
    @26
    chlej2
    ex
    mp3an12
    syl
    imp
    @19
    @52
    @23
    wceq
    @4
    @19
    @52
    cA
    @26
    chj
    co
    #
    @23
    @19
    @37
    @34
    @52
    @57
    wceq
    @38
    mdexch.1
    @26
    cA
    chjcom
    sylancl
    @19
    cA
    cA
    chj
    co
    #
    @11
    chj
    co
    #
    @26
    @57
    @23
    @58
    cA
    @11
    chj
    cA
    mdexch.1
    chjidmi
    oveq1i
    @34
    @34
    @19
    @59
    @57
    wceq
    mdexch.1
    mdexch.1
    cA
    cA
    @11
    chjass
    mp3an12
    @34
    @19
    @26
    @23
    wceq
    mdexch.1
    cA
    @11
    chjcom
    mpan
    3eqtr3a
    eqtrd
    adantr
    sseqtrd
    ad2ant2rl
    eqsstrd
    @28
    @23
    cB
    ssrin
    syl
    eqsstrd
    adantrl
    @22
    @0
    @24
    @15
    wss
    @20
    @22
    @0
    wa
    @24
    @11
    @9
    chj
    co
    #
    @15
    @19
    @12
    @0
    @24
    @60
    wceq
    #
    @19
    @0
    @12
    @61
    @34
    @48
    @19
    @0
    @12
    @61
    wi
    wi
    mdexch.1
    mdexch.2
    @34
    @48
    @19
    w3a
    @0
    @12
    @61
    cA
    cB
    @11
    mdi
    exp32
    mp3an12
    com23
    imp31
    @19
    @60
    @15
    wss
    #
    @12
    @0
    @19
    @9
    @8
    wss
    #
    @62
    cA
    @6
    wss
    @63
    cA
    cC
    mdexch.1
    mdexch.3
    chub2i
    cA
    @6
    cB
    ssrin
    ax-mp
    @9
    cch
    wcel
    #
    @8
    cch
    wcel
    #
    @19
    @63
    @62
    wi
    cA
    cB
    mdexch.1
    mdexch.2
    chincli
    @6
    cB
    @36
    mdexch.2
    chincli
    @64
    @65
    @19
    w3a
    @63
    @62
    @9
    @8
    @11
    chlej2
    ex
    mp3an12
    mpi
    ad2antrr
    eqsstrd
    adantrr
    sstrd
    exp31
    com3r
    3impb
    ralrimiv
    @35
    @48
    @7
    @18
    wb
    @36
    mdexch.2
    vx
    @6
    cB
    mdbr2
    mp2an
    sylibr
    @2
    @4
    @10
    @0
    @20
    @8
    cA
    cC
    chj
    co
    #
    @39
    cin
    #
    @9
    @6
    @66
    cB
    @39
    cC
    cA
    mdexch.3
    mdexch.1
    chjcomi
    @40
    @42
    @39
    cB
    @43
    cB
    @1
    incom
    @44
    3eqtr3ri
    ineq12i
    @20
    @67
    @66
    @1
    cin
    #
    cB
    cin
    @9
    @66
    @1
    cB
    inass
    @20
    @68
    cA
    cB
    @2
    @4
    @68
    cA
    @3
    chj
    co
    #
    cA
    @2
    cA
    @1
    wss
    #
    @68
    @69
    wceq
    #
    cA
    cB
    mdexch.1
    mdexch.2
    chub1i
    @33
    @50
    @34
    @2
    @70
    @71
    wi
    wi
    mdexch.3
    @51
    mdexch.1
    @33
    @50
    @34
    w3a
    @2
    @70
    @71
    cC
    @1
    cA
    mdi
    exp32
    mp3an
    mpi
    @4
    @69
    @3
    cA
    chj
    co
    #
    cA
    cA
    @3
    mdexch.1
    @56
    chjcomi
    @4
    @72
    cA
    wceq
    @3
    cA
    @56
    mdexch.1
    chlejb1i
    biimpi
    syl5eq
    sylan9eq
    ineq1d
    syl5eqr
    syl5eq
    3adant1
    jca
end
