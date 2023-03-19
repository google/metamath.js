include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cpr.mm"
include "csn.mm"
include "csymg.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "symg1bas.mm"
include "ad2antll.mm"
include "cun.mm"
include "df-pr.mm"
include "sneq.mm"
include "uneq1d.mm"
include "adantr.mm"
include "unidm.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "id.mm"
include "opeq12d.mm"
include "preq1d.mm"
include "opex.mm"
include "preqsn.mm"
include "mpbir2an.mm"
include "opeq1.mm"
include "opeq2.mm"
include "preq12d.mm"
include "snex.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "cvv.mm"
include "chash.mm"
include "c2.mm"
include "wne.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "w3a.mm"
include "df-ne.mm"
include "biimpri.mm"
include "anim2i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "ancoms.mm"
include "symg2hash.mm"
include "syl.mm"
include "wf1o.mm"
include "ancri.mm"
include "anim12i.mm"
include "sylbir.mm"
include "f1oprg.mm"
include "imp.mm"
include "syl2anr.mm"
include "wb.mm"
include "eqidd.mm"
include "f1oeq123d.mm"
include "ax-mp.mm"
include "prex.mm"
include "elsymgbas2.mm"
include "f1oprswap.mm"
include "adantl.mm"
include "wo.mm"
include "pm3.2i.mm"
include "wi.mm"
include "opthg2.mm"
include "eqtr.mm"
include "syl6bi.mm"
include "necon3d.mm"
include "com12.mm"
include "opthg.mm"
include "simpl.mm"
include "jca.mm"
include "orcd.mm"
include "prneimg.mm"
include "mpsyl.mm"
include "hash2prd.mm"
include "syl23anc.mm"
include "pm2.61ian.mm"

theorem symg2bas
  let cA: class A
  let cB: class B
  let cG: class G
  let cI: class I
  let cJ: class J
  let cV: class V
  let cW: class W
  assume symg1bas.1: |- G = ( SymGrp ` A )
  assume symg1bas.2: |- B = ( Base ` G )
  assume symg2bas.0: |- A = { I , J }


  assert |- ( ( I e. V /\ J e. W ) -> B = { { <. I , I >. , <. J , J >. } , { <. I , J >. , <. J , I >. } } )

  proof
    cI
    cJ
    wceq
    #
    cI
    cV
    wcel
    #
    cJ
    cW
    wcel
    #
    wa
    #
    cB
    cI
    cI
    cop
    #
    cJ
    cJ
    cop
    #
    cpr
    #
    cI
    cJ
    cop
    #
    cJ
    cI
    cop
    #
    cpr
    #
    cpr
    #
    wceq
    #
    @0
    @3
    wa
    #
    cJ
    csn
    #
    csymg
    cfv
    #
    cbs
    cfv
    #
    @5
    csn
    #
    csn
    #
    cB
    @10
    @2
    @15
    @17
    wceq
    @0
    @1
    @13
    @15
    @14
    cJ
    cW
    @14
    eqid
    @15
    eqid
    @13
    eqid
    symg1bas
    ad2antll
    @12
    cB
    cG
    cbs
    cfv
    #
    @15
    symg1bas.2
    @12
    cG
    @14
    cbs
    @12
    cG
    cA
    csymg
    cfv
    @14
    symg1bas.1
    @12
    cA
    @13
    csymg
    @12
    cA
    cI
    cJ
    cpr
    #
    @13
    symg2bas.0
    @12
    @19
    cI
    csn
    #
    @13
    cun
    #
    @13
    cI
    cJ
    df-pr
    @12
    @21
    @13
    @13
    cun
    #
    @13
    @0
    @21
    @22
    wceq
    @3
    @0
    @20
    @13
    @13
    cI
    cJ
    sneq
    uneq1d
    adantr
    @13
    unidm
    syl6eq
    syl5eq
    syl5eq
    fveq2d
    syl5eq
    fveq2d
    syl5eq
    @12
    @10
    @16
    @16
    cpr
    #
    @17
    @12
    @6
    @16
    @9
    @16
    @12
    @6
    @5
    @5
    cpr
    #
    @16
    @12
    @4
    @5
    @5
    @0
    @4
    @5
    wceq
    @3
    @0
    cI
    cJ
    cI
    cJ
    @0
    id
    #
    @25
    opeq12d
    adantr
    preq1d
    @24
    @16
    wceq
    @5
    @5
    wceq
    #
    @26
    @5
    eqid
    #
    @27
    @5
    @5
    @5
    cJ
    cJ
    opex
    #
    @28
    @28
    preqsn
    mpbir2an
    #
    syl6eq
    @0
    @9
    @16
    wceq
    @3
    @0
    @9
    @24
    @16
    @0
    @7
    @5
    @8
    @5
    cI
    cJ
    cJ
    opeq1
    cI
    cJ
    cJ
    opeq2
    preq12d
    @29
    syl6eq
    adantr
    preq12d
    @23
    @17
    wceq
    @16
    @16
    wceq
    #
    @30
    @16
    eqid
    #
    @31
    @16
    @16
    @16
    @5
    snex
    #
    @32
    @32
    preqsn
    mpbir2an
    syl6eq
    3eqtr4d
    @0
    wn
    #
    @3
    wa
    #
    cB
    cvv
    wcel
    #
    cB
    chash
    cfv
    c2
    wceq
    #
    @6
    cB
    wcel
    #
    @9
    cB
    wcel
    #
    @6
    @9
    wne
    #
    @11
    @35
    @34
    cB
    @18
    cvv
    symg1bas.2
    cG
    cbs
    fvex
    eqeltri
    a1i
    @34
    @1
    @2
    cI
    cJ
    wne
    #
    w3a
    #
    @36
    @3
    @33
    @41
    @3
    @33
    wa
    @3
    @40
    wa
    @41
    @33
    @40
    @3
    @40
    @33
    cI
    cJ
    df-ne
    #
    biimpri
    anim2i
    @1
    @2
    @40
    df-3an
    sylibr
    ancoms
    cA
    cB
    cG
    cI
    cJ
    cV
    cW
    symg1bas.1
    symg1bas.2
    symg2bas.0
    symg2hash
    syl
    @34
    cA
    cA
    @6
    wf1o
    #
    @37
    @34
    @19
    @19
    @6
    wf1o
    #
    @43
    @3
    @1
    @1
    wa
    #
    @2
    @2
    wa
    #
    wa
    #
    @40
    @40
    wa
    #
    @44
    @33
    @1
    @45
    @2
    @46
    @1
    @1
    @1
    id
    ancri
    #
    @2
    @2
    @2
    id
    ancri
    anim12i
    @33
    @40
    @48
    @42
    @40
    @40
    @40
    id
    ancri
    sylbir
    @47
    @48
    @44
    cI
    cI
    cJ
    cJ
    cV
    cV
    cW
    cW
    f1oprg
    imp
    syl2anr
    cA
    @19
    wceq
    #
    @43
    @44
    wb
    symg2bas.0
    @50
    cA
    @19
    cA
    @19
    @6
    @6
    @50
    @6
    eqidd
    @50
    id
    #
    @51
    f1oeq123d
    ax-mp
    sylibr
    @6
    cvv
    wcel
    @37
    @43
    wb
    @4
    @5
    prex
    cA
    cB
    @6
    cG
    cvv
    symg1bas.1
    symg1bas.2
    elsymgbas2
    ax-mp
    sylibr
    @34
    cA
    cA
    @9
    wf1o
    #
    @38
    @3
    @52
    @33
    @3
    @19
    @19
    @9
    wf1o
    #
    @52
    cI
    cJ
    cV
    cW
    f1oprswap
    @50
    @52
    @53
    wb
    symg2bas.0
    @50
    cA
    @19
    cA
    @19
    @9
    @9
    @50
    @9
    eqidd
    @51
    @51
    f1oeq123d
    ax-mp
    sylibr
    adantl
    @9
    cvv
    wcel
    @38
    @52
    wb
    @7
    @8
    prex
    cA
    cB
    @9
    cG
    cvv
    symg1bas.1
    symg1bas.2
    elsymgbas2
    ax-mp
    sylibr
    @4
    cvv
    wcel
    #
    @5
    cvv
    wcel
    #
    wa
    #
    @7
    cvv
    wcel
    #
    @8
    cvv
    wcel
    #
    wa
    #
    wa
    @34
    @4
    @7
    wne
    #
    @4
    @8
    wne
    #
    wa
    #
    @5
    @7
    wne
    @5
    @8
    wne
    wa
    #
    wo
    @39
    @56
    @59
    @54
    @55
    cI
    cI
    opex
    @28
    pm3.2i
    @57
    @58
    cI
    cJ
    opex
    cJ
    cI
    opex
    pm3.2i
    pm3.2i
    @34
    @62
    @63
    @34
    @60
    @61
    @33
    @3
    @60
    @33
    @40
    @3
    @60
    wi
    @42
    @3
    @40
    @60
    @3
    @4
    @7
    cI
    cJ
    @3
    @4
    @7
    wceq
    cI
    cI
    wceq
    #
    @0
    wa
    @0
    cI
    cI
    cI
    cJ
    cV
    cW
    opthg2
    cI
    cI
    cJ
    eqtr
    syl6bi
    necon3d
    com12
    sylbir
    imp
    @33
    @3
    @61
    @33
    @40
    @3
    @61
    wi
    @42
    @3
    @40
    @61
    @3
    @4
    @8
    cI
    cJ
    @3
    @4
    @8
    wceq
    #
    @0
    @64
    wa
    #
    @0
    @3
    @45
    @65
    @66
    wb
    @1
    @45
    @2
    @49
    adantr
    cI
    cI
    cJ
    cI
    cV
    cV
    opthg
    syl
    @0
    @64
    simpl
    syl6bi
    necon3d
    com12
    sylbir
    imp
    jca
    orcd
    @4
    @5
    @7
    @8
    cvv
    cvv
    cvv
    cvv
    prneimg
    mpsyl
    @35
    @36
    wa
    @37
    @38
    @39
    w3a
    @11
    cB
    cvv
    @6
    @9
    hash2prd
    imp
    syl23anc
    pm2.61ian
end
