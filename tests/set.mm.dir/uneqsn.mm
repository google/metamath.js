include "cvv.mm"
include "wcel.mm"
include "cun.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "w3o.mm"
include "wb.mm"
include "wss.mm"
include "wo.mm"
include "eqss.mm"
include "a1i.mm"
include "unss.mm"
include "bicomi.mm"
include "elun.mm"
include "snssg.mm"
include "orbi12d.mm"
include "syl5rbb.mm"
include "bitr2d.mm"
include "anbi12d.mm"
include "wn.mm"
include "or3or.mm"
include "anbi2i.mm"
include "andi3or.mm"
include "bitri.mm"
include "an4.mm"
include "anbi12i.mm"
include "sssn.mm"
include "anbi1d.mm"
include "andir.mm"
include "n0i.mm"
include "syl6bir.mm"
include "con2d.mm"
include "pm4.71d.mm"
include "wi.mm"
include "eqimss2.mm"
include "iman.mm"
include "mpbi.mm"
include "biorfi.mm"
include "syl6rbb.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "3orbi123d.mm"
include "3bitrd.mm"
include "snprc.mm"
include "biimpi.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "pm4.25.mm"
include "orbi1i.mm"
include "syl6rbbr.mm"
include "un00.mm"
include "df-3or.mm"
include "3bitr4g.mm"
include "pm2.61i.mm"

theorem uneqsn
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A u. B ) = { C } <-> ( ( A = { C } /\ B = { C } ) \/ ( A = { C } /\ B = (/) ) \/ ( A = (/) /\ B = { C } ) ) )

  proof
    cC
    cvv
    wcel
    #
    cA
    cB
    cun
    #
    cC
    csn
    #
    wceq
    #
    cA
    @2
    wceq
    #
    cB
    @2
    wceq
    #
    wa
    #
    @4
    cB
    c0
    wceq
    #
    wa
    #
    cA
    c0
    wceq
    #
    @5
    wa
    #
    w3o
    #
    wb
    @0
    @3
    @1
    @2
    wss
    #
    @2
    @1
    wss
    #
    wa
    #
    cA
    @2
    wss
    #
    cB
    @2
    wss
    #
    wa
    #
    @2
    cA
    wss
    #
    @2
    cB
    wss
    #
    wo
    #
    wa
    #
    @11
    @3
    @14
    wb
    @0
    @1
    @2
    eqss
    a1i
    @0
    @12
    @17
    @13
    @20
    @12
    @17
    wb
    @0
    @17
    @12
    cA
    cB
    @2
    unss
    bicomi
    a1i
    @0
    @20
    cC
    @1
    wcel
    #
    @13
    @22
    cC
    cA
    wcel
    #
    cC
    cB
    wcel
    #
    wo
    @0
    @20
    cC
    cA
    cB
    elun
    @0
    @23
    @18
    @24
    @19
    cC
    cA
    cvv
    snssg
    #
    cC
    cB
    cvv
    snssg
    #
    orbi12d
    syl5rbb
    cC
    @1
    cvv
    snssg
    bitr2d
    anbi12d
    @21
    @17
    @18
    @19
    wa
    #
    wa
    #
    @17
    @18
    @19
    wn
    #
    wa
    #
    wa
    #
    @17
    @18
    wn
    #
    @19
    wa
    #
    wa
    #
    w3o
    #
    @0
    @11
    @21
    @17
    @27
    @30
    @33
    w3o
    #
    wa
    @35
    @20
    @36
    @17
    @18
    @19
    or3or
    anbi2i
    @17
    @27
    @30
    @33
    andi3or
    bitri
    @0
    @28
    @6
    @31
    @8
    @34
    @10
    @28
    @6
    wb
    @0
    @28
    @15
    @18
    wa
    #
    @16
    @19
    wa
    #
    wa
    #
    @6
    @15
    @16
    @18
    @19
    an4
    @6
    @39
    @4
    @37
    @5
    @38
    cA
    @2
    eqss
    #
    cB
    @2
    eqss
    #
    anbi12i
    bicomi
    bitri
    a1i
    @31
    @37
    @16
    @29
    wa
    #
    wa
    @0
    @8
    @15
    @16
    @18
    @29
    an4
    @0
    @37
    @4
    @42
    @7
    @37
    @4
    wb
    @0
    @4
    @37
    @40
    bicomi
    a1i
    @0
    @42
    @7
    @5
    wo
    #
    @29
    wa
    #
    @7
    @0
    @16
    @43
    @29
    @16
    @43
    wb
    @0
    cB
    cC
    sssn
    a1i
    anbi1d
    @44
    @7
    @29
    wa
    #
    @5
    @29
    wa
    #
    wo
    #
    @0
    @7
    @7
    @5
    @29
    andir
    @0
    @7
    @45
    @47
    @0
    @7
    @29
    @0
    @19
    @7
    @0
    @19
    @24
    @7
    wn
    @26
    cB
    cC
    n0i
    syl6bir
    con2d
    pm4.71d
    @46
    @45
    @5
    @19
    wi
    @46
    wn
    @2
    cB
    eqimss2
    @5
    @19
    iman
    mpbi
    biorfi
    syl6rbb
    syl5bb
    bitrd
    anbi12d
    syl5bb
    @34
    @15
    @32
    wa
    #
    @38
    wa
    @0
    @10
    @15
    @16
    @32
    @19
    an4
    @0
    @48
    @9
    @38
    @5
    @0
    @48
    @9
    @4
    wo
    #
    @32
    wa
    #
    @9
    @0
    @15
    @49
    @32
    @15
    @49
    wb
    @0
    cA
    cC
    sssn
    a1i
    anbi1d
    @50
    @9
    @32
    wa
    #
    @4
    @32
    wa
    #
    wo
    #
    @0
    @9
    @9
    @4
    @32
    andir
    @0
    @9
    @51
    @53
    @0
    @9
    @32
    @0
    @18
    @9
    @0
    @18
    @23
    @9
    wn
    @25
    cA
    cC
    n0i
    syl6bir
    con2d
    pm4.71d
    @52
    @51
    @4
    @18
    wi
    @52
    wn
    @2
    cA
    eqimss2
    @4
    @18
    iman
    mpbi
    biorfi
    syl6rbb
    syl5bb
    bitrd
    @38
    @5
    wb
    @0
    @5
    @38
    @41
    bicomi
    a1i
    anbi12d
    syl5bb
    3orbi123d
    syl5bb
    3bitrd
    @0
    wn
    #
    @3
    @1
    c0
    wceq
    #
    @11
    @54
    @2
    c0
    @1
    @54
    @2
    c0
    wceq
    cC
    snprc
    biimpi
    #
    eqeq2d
    @54
    @9
    @7
    wa
    #
    @6
    @8
    wo
    #
    @10
    wo
    #
    @55
    @11
    @54
    @59
    @57
    @57
    wo
    #
    @57
    wo
    #
    @57
    @54
    @58
    @60
    @10
    @57
    @54
    @6
    @57
    @8
    @57
    @54
    @4
    @9
    @5
    @7
    @54
    @2
    c0
    cA
    @56
    eqeq2d
    #
    @54
    @2
    c0
    cB
    @56
    eqeq2d
    #
    anbi12d
    @54
    @4
    @9
    @7
    @62
    anbi1d
    orbi12d
    @54
    @5
    @7
    @9
    @63
    anbi2d
    orbi12d
    @57
    @60
    @61
    @57
    pm4.25
    #
    @57
    @60
    @57
    @64
    orbi1i
    bitri
    syl6rbbr
    @57
    @55
    cA
    cB
    un00
    bicomi
    @6
    @8
    @10
    df-3or
    3bitr4g
    bitrd
    pm2.61i
end
