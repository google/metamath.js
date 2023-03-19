include "cpths.mm"
include "cfv.mm"
include "wbr.mm"
include "c1.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "wne.mm"
include "w3a.mm"
include "ctrls.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "cpr.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "ispth.mm"
include "cwlks.mm"
include "cvtx.mm"
include "wf.mm"
include "trliswlk.mm"
include "eqid.mm"
include "wlkp.mm"
include "w3o.mm"
include "elfz0lmr.mm"
include "wa.mm"
include "wnel.mm"
include "cn0.mm"
include "wb.mm"
include "cn.mm"
include "clt.mm"
include "elfzo1.mm"
include "nnnn0.mm"
include "3ad2ant2.mm"
include "sylbi.mm"
include "adantl.mm"
include "fvinim0ffz.mm"
include "sylan2.mm"
include "wn.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "ad2antrl.mm"
include "cdm.mm"
include "ffun.mm"
include "adantr.mm"
include "fdm.mm"
include "fzo0ss1.mm"
include "fzossfz.mm"
include "sstri.mm"
include "sseli.mm"
include "eleq2.mm"
include "syl5ibr.mm"
include "syl.mm"
include "imp.mm"
include "jca.mm"
include "adantrl.mm"
include "simprr.mm"
include "funfvima.mm"
include "sylc.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "sylbid.mm"
include "nnel.mm"
include "syl6ibr.mm"
include "necon2ad.mm"
include "adantrd.mm"
include "ex.mm"
include "com23.mm"
include "a1d.mm"
include "3imp.mm"
include "com12.mm"
include "fvres.mm"
include "eqcomd.mm"
include "eqeq12d.mm"
include "wf1.mm"
include "wss.mm"
include "fssres.mm"
include "mpan2.mm"
include "df-f1.mm"
include "biimpri.mm"
include "sylan.mm"
include "3adant3.mm"
include "simpr.mm"
include "ancomd.mm"
include "f1veqaeq.mm"
include "syl2an2r.mm"
include "ancoms.mm"
include "necon3d.mm"
include "adantld.mm"
include "3jaoi.mm"
include "3imp21.mm"
include "3exp.mm"
include "3syl.mm"

theorem pthdivtx
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J


  assert |- ( ( F ( Paths ` G ) P /\ ( I e. ( 1 ..^ ( # ` F ) ) /\ J e. ( 0 ... ( # ` F ) ) /\ I =/= J ) ) -> ( P ` I ) =/= ( P ` J ) )

  proof
    cF
    cP
    cG
    cpths
    cfv
    wbr
    #
    cI
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    #
    cJ
    cc0
    @1
    cfz
    co
    #
    wcel
    #
    cI
    cJ
    wne
    #
    w3a
    #
    cI
    cP
    cfv
    #
    cJ
    cP
    cfv
    #
    wne
    #
    @0
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cP
    @2
    cres
    #
    ccnv
    wfun
    #
    cP
    cc0
    @1
    cpr
    cima
    cP
    @2
    cima
    #
    cin
    c0
    wceq
    #
    w3a
    @7
    @10
    wi
    #
    cP
    cF
    cG
    ispth
    @11
    @13
    @15
    @16
    @11
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    @4
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    @13
    @15
    @16
    wi
    wi
    cP
    cF
    cG
    trliswlk
    cP
    cF
    cG
    @17
    @17
    eqid
    wlkp
    @18
    @13
    @15
    @16
    @7
    @18
    @13
    @15
    w3a
    #
    @10
    @5
    @3
    @6
    @19
    @10
    wi
    #
    @5
    cJ
    cc0
    wceq
    #
    cJ
    @2
    wcel
    #
    cJ
    @1
    wceq
    #
    w3o
    @3
    @6
    @20
    wi
    #
    wi
    #
    cJ
    @1
    elfz0lmr
    @21
    @25
    @22
    @23
    @21
    @3
    @24
    @21
    @3
    wa
    #
    @20
    @6
    @19
    @26
    @10
    @18
    @13
    @15
    @26
    @10
    wi
    #
    @18
    @15
    @27
    wi
    @13
    @18
    @26
    @15
    @10
    @18
    @26
    @15
    @10
    wi
    #
    @18
    @26
    wa
    #
    @15
    cc0
    cP
    cfv
    #
    @14
    wnel
    #
    @1
    cP
    cfv
    #
    @14
    wnel
    #
    wa
    #
    @10
    @26
    @18
    @1
    cn0
    wcel
    #
    @15
    @34
    wb
    #
    @3
    @35
    @21
    @3
    cI
    cn
    wcel
    #
    @1
    cn
    wcel
    #
    cI
    @1
    clt
    wbr
    #
    w3a
    @35
    @1
    cI
    elfzo1
    @38
    @37
    @35
    @39
    @1
    nnnn0
    3ad2ant2
    sylbi
    #
    adantl
    cP
    @1
    @17
    fvinim0ffz
    #
    sylan2
    @29
    @31
    @10
    @33
    @29
    @31
    @8
    @9
    @29
    @8
    @9
    wceq
    #
    @30
    @14
    wcel
    #
    @31
    wn
    @29
    @42
    @8
    @30
    wceq
    #
    @43
    @21
    @42
    @44
    wb
    @18
    @3
    @21
    @9
    @30
    @8
    cJ
    cc0
    cP
    fveq2
    eqeq2d
    ad2antrl
    @29
    @8
    @14
    wcel
    #
    @44
    @43
    @29
    cP
    wfun
    #
    cI
    cP
    cdm
    #
    wcel
    #
    wa
    #
    @3
    @45
    @18
    @3
    @49
    @21
    @18
    @3
    wa
    @46
    @48
    @18
    @46
    @3
    @4
    @17
    cP
    ffun
    adantr
    @18
    @3
    @48
    @18
    @47
    @4
    wceq
    #
    @3
    @48
    wi
    @4
    @17
    cP
    fdm
    @3
    @48
    @50
    cI
    @4
    wcel
    @2
    @4
    cI
    @2
    cc0
    @1
    cfzo
    co
    @4
    @1
    fzo0ss1
    cc0
    @1
    fzossfz
    sstri
    #
    sseli
    @47
    @4
    cI
    eleq2
    syl5ibr
    syl
    imp
    jca
    #
    adantrl
    @18
    @21
    @3
    simprr
    @2
    cI
    cP
    funfvima
    #
    sylc
    @8
    @30
    @14
    eleq1
    syl5ibcom
    sylbid
    @30
    @14
    nnel
    syl6ibr
    necon2ad
    adantrd
    sylbid
    ex
    com23
    a1d
    3imp
    com12
    a1d
    ex
    @22
    @3
    @24
    @22
    @3
    wa
    #
    @19
    @6
    @10
    @54
    @19
    @6
    @10
    wi
    @54
    @19
    wa
    @8
    @9
    cI
    cJ
    @19
    @54
    @42
    cI
    cJ
    wceq
    #
    wi
    @19
    @54
    wa
    #
    @42
    cI
    @12
    cfv
    #
    cJ
    @12
    cfv
    #
    wceq
    #
    @55
    @56
    @8
    @57
    @9
    @58
    @56
    @57
    @8
    @54
    @57
    @8
    wceq
    #
    @19
    @3
    @60
    @22
    cI
    @2
    cP
    fvres
    adantl
    adantl
    eqcomd
    @56
    @58
    @9
    @22
    @58
    @9
    wceq
    @19
    @3
    cJ
    @2
    cP
    fvres
    ad2antrl
    eqcomd
    eqeq12d
    @19
    @2
    @17
    @12
    wf1
    #
    @54
    @3
    @22
    wa
    @59
    @55
    wi
    @18
    @13
    @61
    @15
    @18
    @2
    @17
    @12
    wf
    #
    @13
    @61
    @18
    @2
    @4
    wss
    @62
    @51
    @4
    @17
    @2
    cP
    fssres
    mpan2
    @61
    @62
    @13
    wa
    @2
    @17
    @12
    df-f1
    biimpri
    sylan
    3adant3
    @56
    @22
    @3
    @19
    @54
    simpr
    ancomd
    @2
    @17
    cI
    cJ
    @12
    f1veqaeq
    syl2an2r
    sylbid
    ancoms
    necon3d
    ex
    com23
    ex
    @23
    @3
    @24
    @23
    @3
    wa
    #
    @20
    @6
    @19
    @63
    @10
    @18
    @13
    @15
    @63
    @10
    wi
    #
    @18
    @15
    @64
    wi
    @13
    @18
    @63
    @15
    @10
    @18
    @63
    @28
    @18
    @63
    wa
    #
    @15
    @34
    @10
    @63
    @18
    @35
    @36
    @3
    @35
    @23
    @40
    adantl
    @41
    sylan2
    @65
    @33
    @10
    @31
    @65
    @33
    @8
    @9
    @65
    @42
    @32
    @14
    wcel
    #
    @33
    wn
    @65
    @42
    @8
    @32
    wceq
    #
    @66
    @23
    @42
    @67
    wb
    @18
    @3
    @23
    @9
    @32
    @8
    cJ
    @1
    cP
    fveq2
    eqeq2d
    ad2antrl
    @65
    @45
    @67
    @66
    @65
    @49
    @3
    @45
    @18
    @3
    @49
    @23
    @52
    adantrl
    @18
    @23
    @3
    simprr
    @53
    sylc
    @8
    @32
    @14
    eleq1
    syl5ibcom
    sylbid
    @32
    @14
    nnel
    syl6ibr
    necon2ad
    adantld
    sylbid
    ex
    com23
    a1d
    3imp
    com12
    a1d
    ex
    3jaoi
    syl
    3imp21
    com12
    3exp
    3syl
    3imp
    sylbi
    imp
end
