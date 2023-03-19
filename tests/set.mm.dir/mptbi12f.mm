include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "copab.mm"
include "cmpt.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "nfeq.mm"
include "eleq2.mm"
include "alrimi.mm"
include "ax-5.mm"
include "alimi.mm"
include "syl.mm"
include "eqeq2.mm"
include "alrimiv.mm"
include "ralimi.mm"
include "df-ral.mm"
include "sylib.mm"
include "19.21v.mm"
include "albii.mm"
include "sylibr.mm"
include "id.mm"
include "alanimi.mm"
include "syl2an.mm"
include "wn.mm"
include "wfal.mm"
include "tsan2.mm"
include "ord.mm"
include "wo.mm"
include "tsbi2.mm"
include "a1dd.mm"
include "ax-1.mm"
include "contrd.mm"
include "a1d.mm"
include "cnf1dd.mm"
include "simplim.mm"
include "tsbi3.mm"
include "tsan3.mm"
include "cnfn2dd.mm"
include "mpdd.mm"
include "notnotr.mm"
include "a1i.mm"
include "jcad.mm"
include "tsim3.mm"
include "cnf2dd.mm"
include "tsbi1.mm"
include "tsbi4.mm"
include "cnfn1dd.mm"
include "tsan1.mm"
include "or32dd.mm"
include "efald2.mm"
include "2alimi.mm"
include "eqopab2b.mm"
include "df-mpt.mm"
include "3eqtr4g.mm"

theorem mptbi12f
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cE: class E
  let vy: setvar y
  assume mptbi12f.1: |- F/_ x A
  assume mptbi12f.2: |- F/_ x B


  assert |- ( ( A = B /\ A. x e. A D = E ) -> ( x e. A |-> D ) = ( x e. B |-> E ) )

  proof
    cA
    cB
    wceq
    #
    cD
    cE
    wceq
    #
    vx
    cA
    wral
    #
    wa
    #
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cD
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    @4
    cB
    wcel
    #
    @6
    cE
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    vx
    cA
    cD
    cmpt
    vx
    cB
    cE
    cmpt
    @3
    @8
    @12
    wb
    #
    vy
    wal
    vx
    wal
    #
    @9
    @13
    wceq
    @3
    @5
    @10
    wb
    #
    @5
    @7
    @11
    wb
    #
    wi
    #
    wa
    #
    vy
    wal
    #
    vx
    wal
    #
    @15
    @0
    @16
    vy
    wal
    #
    vx
    wal
    #
    @18
    vy
    wal
    #
    vx
    wal
    #
    @21
    @2
    @0
    @16
    vx
    wal
    @23
    @0
    @16
    vx
    vx
    cA
    cB
    mptbi12f.1
    mptbi12f.2
    nfeq
    cA
    cB
    @4
    eleq2
    alrimi
    @16
    @22
    vx
    @16
    vy
    ax-5
    alimi
    syl
    @2
    @5
    @17
    vy
    wal
    #
    wi
    #
    vx
    wal
    #
    @25
    @2
    @26
    vx
    cA
    wral
    @28
    @1
    @26
    vx
    cA
    @1
    @17
    vy
    cD
    cE
    @6
    eqeq2
    alrimiv
    ralimi
    @26
    vx
    cA
    df-ral
    sylib
    @24
    @27
    vx
    @5
    @17
    vy
    19.21v
    albii
    sylibr
    @22
    @24
    @20
    vx
    @16
    @18
    @19
    vy
    @19
    id
    alanimi
    alanimi
    syl2an
    @19
    @14
    vx
    vy
    @19
    @14
    wi
    #
    @29
    wn
    #
    wfal
    @17
    @30
    wfal
    wn
    #
    @5
    @17
    @30
    @5
    @31
    @30
    @5
    @12
    @30
    @5
    wn
    #
    @8
    @12
    @30
    @5
    @8
    wn
    #
    @5
    @7
    @30
    tsan2
    ord
    @30
    @8
    @12
    wo
    #
    @32
    @30
    @34
    @29
    @30
    @34
    wn
    #
    @14
    @19
    @30
    @34
    @14
    @8
    @12
    @30
    tsbi2
    ord
    a1dd
    @30
    @35
    ax-1
    contrd
    #
    a1d
    cnf1dd
    @30
    @32
    @10
    @12
    wn
    #
    @30
    @5
    @10
    wn
    #
    @30
    @5
    @38
    wo
    #
    @19
    @30
    @19
    @39
    wn
    #
    @19
    @14
    simplim
    #
    a1d
    @30
    @40
    @16
    @19
    wn
    #
    @30
    @39
    @16
    wn
    #
    @5
    @10
    @30
    tsbi3
    ord
    @30
    @16
    @42
    wo
    #
    @40
    @16
    @18
    @30
    tsan2
    #
    a1d
    cnf1dd
    contrd
    #
    ord
    @30
    @10
    @37
    wo
    #
    @32
    @10
    @11
    @30
    tsan2
    #
    a1d
    cnf1dd
    contrd
    a1d
    #
    @30
    @31
    @18
    @19
    @30
    @19
    @31
    @41
    a1d
    #
    @30
    @18
    @42
    wo
    #
    @31
    @16
    @18
    @30
    tsan3
    #
    a1d
    cnfn2dd
    mpdd
    @30
    @31
    @7
    @17
    wn
    #
    @30
    @31
    @7
    @8
    @30
    @31
    @8
    @12
    @30
    @37
    @31
    @30
    @37
    @8
    @30
    @37
    wn
    #
    @5
    @7
    @30
    @54
    @5
    @10
    @30
    @54
    @10
    @12
    @54
    @12
    wi
    @30
    @12
    notnotr
    a1i
    #
    @30
    @47
    @54
    @48
    a1d
    cnfn2dd
    @30
    @39
    @54
    @46
    a1d
    cnfn2dd
    #
    @30
    @54
    @7
    @11
    @30
    @54
    @11
    @12
    @55
    @30
    @11
    @37
    wo
    @54
    @10
    @11
    @30
    tsan3
    a1d
    cnfn2dd
    @30
    @54
    @7
    @11
    wn
    #
    wo
    #
    @17
    @30
    @54
    @5
    @17
    @56
    @30
    @54
    @18
    @19
    @30
    @19
    @54
    @41
    a1d
    @30
    @51
    @54
    @52
    a1d
    cnfn2dd
    mpdd
    @30
    @58
    @53
    wo
    @54
    @7
    @11
    @30
    tsbi3
    a1d
    cnfn2dd
    cnfn2dd
    jcad
    @30
    @54
    @33
    @12
    @55
    @30
    @54
    @33
    @37
    wo
    #
    @14
    @30
    @54
    @14
    wn
    #
    @29
    @30
    @54
    ax-1
    @30
    @60
    @29
    wo
    @54
    @19
    @14
    @30
    tsim3
    a1d
    cnf2dd
    @30
    @59
    @14
    wo
    @54
    @8
    @12
    @30
    tsbi1
    a1d
    cnf2dd
    cnfn2dd
    contrd
    a1d
    #
    @30
    @34
    @31
    @36
    a1d
    cnf2dd
    @30
    @7
    @33
    wo
    @31
    @5
    @7
    @30
    tsan3
    a1d
    cnfn2dd
    @30
    @31
    @7
    wn
    #
    @53
    wo
    @11
    @30
    @31
    @10
    @57
    @30
    @31
    @5
    @10
    @49
    @30
    @31
    @32
    @10
    wo
    #
    @16
    @30
    @31
    @16
    @19
    @50
    @30
    @44
    @31
    @45
    a1d
    cnfn2dd
    @30
    @63
    @43
    wo
    @31
    @5
    @10
    @30
    tsbi4
    a1d
    cnfn2dd
    cnfn1dd
    @30
    @31
    @38
    @57
    wo
    #
    @12
    @61
    @30
    @64
    @12
    wo
    @31
    @10
    @11
    @30
    tsan1
    a1d
    cnf2dd
    cnfn1dd
    @30
    @31
    @62
    @11
    @53
    @30
    @62
    @11
    wo
    @53
    wo
    @31
    @7
    @11
    @30
    tsbi4
    a1d
    or32dd
    cnf2dd
    cnfn1dd
    contrd
    efald2
    2alimi
    syl
    @8
    @12
    vx
    vy
    eqopab2b
    sylibr
    vx
    vy
    cA
    cD
    df-mpt
    vx
    vy
    cB
    cE
    df-mpt
    3eqtr4g
end
