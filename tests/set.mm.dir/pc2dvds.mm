include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "cpc.mm"
include "co.mm"
include "cle.mm"
include "cprime.mm"
include "wral.mm"
include "w3a.mm"
include "pcdvdstr.mm"
include "ancoms.mm"
include "ralrimiva.mm"
include "3expia.mm"
include "wi.mm"
include "cc0.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "breq1.mm"
include "imbi12d.mm"
include "wne.mm"
include "wn.mm"
include "cabs.mm"
include "cfv.mm"
include "cgcd.mm"
include "cdiv.mm"
include "c1.mm"
include "c2.mm"
include "cuz.mm"
include "wo.mm"
include "cn.mm"
include "clt.mm"
include "gcddvds.mm"
include "simpld.mm"
include "wb.mm"
include "gcdcl.mm"
include "nn0zd.mm"
include "simpl.mm"
include "dvdsabsb.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "adantr.mm"
include "necon3ai.mm"
include "gcdn0cl.mm"
include "sylan2.mm"
include "nnzd.mm"
include "nnne0d.mm"
include "nnabscl.mm"
include "adantlr.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "cr.mm"
include "nnre.mm"
include "nngt0.mm"
include "jca.mm"
include "divgt0.mm"
include "syl2an.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "elnn1uz2.mm"
include "sylib.mm"
include "simprd.mm"
include "syl5ibcom.mm"
include "cmul.mm"
include "nncnd.mm"
include "1cnd.mm"
include "divmuld.mm"
include "mulid1d.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "absdvdsb.mm"
include "3imtr4d.mm"
include "wrex.mm"
include "exprmfct.mm"
include "cmin.mm"
include "simprl.mm"
include "pcdiv.mm"
include "syl121anc.mm"
include "cq.mm"
include "simplll.mm"
include "zq.mm"
include "syl.mm"
include "pcabs.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "simprr.mm"
include "pcelnn.mm"
include "mpbird.mm"
include "eqeltrrd.mm"
include "pccld.mm"
include "cn0.mm"
include "simplr.mm"
include "pczcl.mm"
include "syl12anc.mm"
include "znnsub.mm"
include "nn0red.mm"
include "ltnled.mm"
include "cif.mm"
include "simpllr.mm"
include "nprmdvds1.mm"
include "ad2antrl.mm"
include "gcdid0.mm"
include "oveq2d.mm"
include "cc.mm"
include "dividd.mm"
include "breq2d.mm"
include "mtbird.mm"
include "necon3bd.mm"
include "mpd.mm"
include "lemin.mm"
include "pcgcd.mm"
include "leidd.mm"
include "biantrurd.mm"
include "3bitr4rd.mm"
include "expr.mm"
include "reximdva.mm"
include "rexnal.mm"
include "syl6ib.mm"
include "syl5.mm"
include "orim12d.mm"
include "ord.mm"
include "con4d.mm"
include "c0.mm"
include "2prm.mm"
include "ne0ii.mm"
include "r19.2z.mm"
include "mpan.mm"
include "cpnf.mm"
include "cxr.mm"
include "id.mm"
include "adantl.mm"
include "pcxcl.mm"
include "syl2anr.mm"
include "pnfge.mm"
include "pc0.mm"
include "pnfxr.mm"
include "xrletri3.mm"
include "sylancl.mm"
include "3bitr4d.mm"
include "pnfnre.mm"
include "neli.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "adantll.mm"
include "an4s.mm"
include "necon1bd.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "0dvds.mm"
include "sylibrd.mm"
include "pm2.61ne.mm"
include "impbid.mm"

theorem pc2dvds
  let cA: class A
  let cB: class B
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y

  disjoint A p
  disjoint B p
  disjoint p x
  disjoint p y
  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> ( A || B <-> A. p e. Prime ( p pCnt A ) <_ ( p pCnt B ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cA
    cB
    cdvds
    wbr
    #
    vp
    cv
    #
    cA
    cpc
    co
    #
    @4
    cB
    cpc
    co
    #
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    @0
    @1
    @3
    @8
    @0
    @1
    @3
    w3a
    #
    @7
    vp
    cprime
    @4
    cprime
    wcel
    #
    @9
    @7
    cA
    cB
    @4
    pcdvdstr
    ancoms
    ralrimiva
    3expia
    @2
    @8
    @3
    wi
    @4
    cc0
    cpc
    co
    #
    @6
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    cc0
    cB
    cdvds
    wbr
    #
    wi
    cA
    cc0
    cA
    cc0
    wceq
    #
    @8
    @13
    @3
    @14
    @15
    @7
    @12
    vp
    cprime
    @15
    @5
    @11
    @6
    cle
    cA
    cc0
    @4
    cpc
    oveq2
    breq1d
    ralbidv
    cA
    cc0
    cB
    cdvds
    breq1
    imbi12d
    @2
    cA
    cc0
    wne
    #
    wa
    #
    @3
    @8
    @17
    @3
    @8
    wn
    #
    @17
    cA
    cabs
    cfv
    #
    cA
    cB
    cgcd
    co
    #
    cdiv
    co
    #
    c1
    wceq
    #
    @21
    c2
    cuz
    cfv
    wcel
    #
    wo
    #
    @3
    @18
    wo
    @17
    @21
    cn
    wcel
    #
    @24
    @17
    @21
    cz
    wcel
    #
    cc0
    @21
    clt
    wbr
    #
    @25
    @17
    @20
    @19
    cdvds
    wbr
    #
    @26
    @2
    @28
    @16
    @2
    @20
    cA
    cdvds
    wbr
    #
    @28
    @2
    @29
    @20
    cB
    cdvds
    wbr
    #
    cA
    cB
    gcddvds
    #
    simpld
    @2
    @20
    cz
    wcel
    #
    @0
    @29
    @28
    wb
    @2
    @20
    cA
    cB
    gcdcl
    nn0zd
    @0
    @1
    simpl
    @20
    cA
    dvdsabsb
    syl2anc
    mpbid
    adantr
    @17
    @32
    @20
    cc0
    wne
    @19
    cz
    wcel
    #
    @28
    @26
    wb
    @17
    @20
    @16
    @2
    @15
    cB
    cc0
    wceq
    #
    wa
    #
    wn
    @20
    cn
    wcel
    #
    @35
    cA
    cc0
    @15
    @34
    simpl
    necon3ai
    cA
    cB
    gcdn0cl
    sylan2
    #
    nnzd
    @17
    @20
    @37
    nnne0d
    #
    @17
    @19
    @0
    @16
    @19
    cn
    wcel
    #
    @1
    cA
    nnabscl
    adantlr
    #
    nnzd
    @20
    @19
    dvdsval2
    syl3anc
    mpbid
    @17
    @39
    @36
    @27
    @40
    @37
    @39
    @19
    cr
    wcel
    #
    cc0
    @19
    clt
    wbr
    #
    wa
    @20
    cr
    wcel
    #
    cc0
    @20
    clt
    wbr
    #
    wa
    @27
    @36
    @39
    @41
    @42
    @19
    nnre
    @19
    nngt0
    jca
    @36
    @43
    @44
    @20
    nnre
    @20
    nngt0
    jca
    @19
    @20
    divgt0
    syl2an
    syl2anc
    @21
    elnnz
    sylanbrc
    #
    @21
    elnn1uz2
    sylib
    @17
    @22
    @3
    @23
    @18
    @17
    @20
    @19
    wceq
    #
    @19
    cB
    cdvds
    wbr
    #
    @22
    @3
    @17
    @30
    @46
    @47
    @2
    @30
    @16
    @2
    @29
    @30
    @31
    simprd
    adantr
    @20
    @19
    cB
    cdvds
    breq1
    syl5ibcom
    @17
    @22
    @20
    c1
    cmul
    co
    #
    @19
    wceq
    @46
    @17
    @19
    @20
    c1
    @17
    @19
    @40
    nncnd
    #
    @17
    @20
    @37
    nncnd
    #
    @17
    1cnd
    @38
    divmuld
    @17
    @48
    @20
    @19
    @17
    @20
    @50
    mulid1d
    eqeq1d
    bitrd
    @2
    @3
    @47
    wb
    @16
    cA
    cB
    absdvdsb
    adantr
    3imtr4d
    @23
    @4
    @21
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    @17
    @18
    @21
    vp
    exprmfct
    @17
    @52
    @7
    wn
    #
    vp
    cprime
    wrex
    @18
    @17
    @51
    @53
    vp
    cprime
    @17
    @10
    @51
    @53
    @17
    @10
    @51
    wa
    #
    wa
    #
    @7
    @5
    @4
    @20
    cpc
    co
    #
    cle
    wbr
    #
    @55
    @56
    @5
    clt
    wbr
    #
    @57
    wn
    @55
    @58
    @5
    @56
    cmin
    co
    #
    cn
    wcel
    #
    @55
    @4
    @21
    cpc
    co
    #
    @59
    cn
    @55
    @61
    @4
    @19
    cpc
    co
    #
    @56
    cmin
    co
    #
    @59
    @55
    @10
    @33
    @19
    cc0
    wne
    @36
    @61
    @63
    wceq
    @17
    @10
    @51
    simprl
    #
    @55
    @19
    @17
    @39
    @54
    @40
    adantr
    #
    nnzd
    @55
    @19
    @65
    nnne0d
    #
    @17
    @36
    @54
    @37
    adantr
    #
    @19
    @20
    @4
    pcdiv
    syl121anc
    @55
    @62
    @5
    @56
    cmin
    @55
    @10
    cA
    cq
    wcel
    #
    @62
    @5
    wceq
    @64
    @55
    @0
    @68
    @0
    @1
    @16
    @54
    simplll
    #
    cA
    zq
    syl
    cA
    @4
    pcabs
    syl2anc
    oveq1d
    eqtrd
    @55
    @61
    cn
    wcel
    #
    @51
    @17
    @10
    @51
    simprr
    #
    @55
    @10
    @25
    @70
    @51
    wb
    @64
    @17
    @25
    @54
    @45
    adantr
    @4
    @21
    pcelnn
    syl2anc
    mpbird
    eqeltrrd
    @55
    @56
    cz
    wcel
    @5
    cz
    wcel
    @58
    @60
    wb
    @55
    @56
    @55
    @4
    @20
    @64
    @67
    pccld
    #
    nn0zd
    @55
    @5
    @55
    @10
    @0
    @16
    @5
    cn0
    wcel
    @64
    @69
    @2
    @16
    @54
    simplr
    @4
    cA
    pczcl
    syl12anc
    #
    nn0zd
    @56
    @5
    znnsub
    syl2anc
    mpbird
    @55
    @56
    @5
    @55
    @56
    @72
    nn0red
    @55
    @5
    @73
    nn0red
    #
    ltnled
    mpbid
    @55
    @5
    @7
    @5
    @6
    cif
    #
    cle
    wbr
    #
    @5
    @5
    cle
    wbr
    #
    @7
    wa
    #
    @57
    @7
    @55
    @5
    cr
    wcel
    #
    @79
    @6
    cr
    wcel
    #
    @76
    @78
    wb
    @74
    @74
    @55
    @6
    @55
    @10
    @1
    cB
    cc0
    wne
    #
    @6
    cn0
    wcel
    @64
    @0
    @1
    @16
    @54
    simpllr
    #
    @55
    @4
    @19
    cA
    cc0
    cgcd
    co
    #
    cdiv
    co
    #
    cdvds
    wbr
    #
    wn
    @81
    @55
    @85
    @4
    c1
    cdvds
    wbr
    #
    @10
    @86
    wn
    @17
    @51
    @4
    nprmdvds1
    ad2antrl
    @55
    @84
    c1
    @4
    cdvds
    @55
    @84
    @19
    @19
    cdiv
    co
    c1
    @55
    @83
    @19
    @19
    cdiv
    @55
    @0
    @83
    @19
    wceq
    @69
    cA
    gcdid0
    syl
    oveq2d
    @55
    @19
    @17
    @19
    cc
    wcel
    @54
    @49
    adantr
    @66
    dividd
    eqtrd
    breq2d
    mtbird
    @55
    @85
    cB
    cc0
    @55
    @51
    @34
    @85
    @71
    @34
    @21
    @84
    @4
    cdvds
    @34
    @20
    @83
    @19
    cdiv
    cB
    cc0
    cA
    cgcd
    oveq2
    oveq2d
    breq2d
    syl5ibcom
    necon3bd
    mpd
    @4
    cB
    pczcl
    #
    syl12anc
    nn0red
    @5
    @5
    @6
    lemin
    syl3anc
    @55
    @56
    @75
    @5
    cle
    @55
    @10
    @0
    @1
    @56
    @75
    wceq
    @64
    @69
    @82
    cA
    cB
    @4
    pcgcd
    syl3anc
    breq2d
    @55
    @77
    @7
    @55
    @5
    @74
    leidd
    biantrurd
    3bitr4rd
    mtbird
    expr
    reximdva
    @7
    vp
    cprime
    rexnal
    syl6ib
    syl5
    orim12d
    mpd
    ord
    con4d
    @13
    @12
    vp
    cprime
    wrex
    #
    @2
    @14
    cprime
    c0
    wne
    @13
    @88
    c2
    cprime
    2prm
    ne0ii
    @12
    vp
    cprime
    r19.2z
    mpan
    @2
    @88
    @34
    @14
    @2
    @12
    @34
    vp
    cprime
    @2
    @10
    wa
    #
    @12
    @6
    cpnf
    wceq
    #
    @34
    @89
    cpnf
    @6
    cle
    wbr
    #
    @6
    cpnf
    cle
    wbr
    #
    @91
    wa
    #
    @12
    @90
    @89
    @92
    @91
    @89
    @6
    cxr
    wcel
    #
    @92
    @10
    @10
    cB
    cq
    wcel
    #
    @94
    @2
    @10
    id
    @1
    @95
    @0
    cB
    zq
    adantl
    @4
    cB
    pcxcl
    syl2anr
    #
    @6
    pnfge
    syl
    biantrurd
    @89
    @11
    cpnf
    @6
    cle
    @10
    @11
    cpnf
    wceq
    @2
    @4
    pc0
    adantl
    breq1d
    @89
    @94
    cpnf
    cxr
    wcel
    @90
    @93
    wb
    @96
    pnfxr
    @6
    cpnf
    xrletri3
    sylancl
    3bitr4d
    @90
    @80
    wn
    @89
    @34
    @90
    @80
    cpnf
    cr
    wcel
    cpnf
    cr
    pnfnre
    neli
    @6
    cpnf
    cr
    eleq1
    mtbiri
    @89
    @80
    cB
    cc0
    @2
    @10
    @81
    @80
    @0
    @10
    @1
    @81
    @80
    @10
    @1
    @81
    wa
    #
    @80
    @0
    @10
    @97
    wa
    @6
    @87
    nn0red
    adantll
    an4s
    expr
    necon1bd
    syl5
    sylbid
    rexlimdva
    @1
    @14
    @34
    wb
    @0
    cB
    0dvds
    adantl
    sylibrd
    syl5
    pm2.61ne
    impbid
end
