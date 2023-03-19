include "cgrp.mm"
include "wcel.mm"
include "cfn.mm"
include "cprime.mm"
include "w3a.mm"
include "cslw.mm"
include "co.mm"
include "csubg.mm"
include "cfv.mm"
include "chash.mm"
include "cpc.mm"
include "cexp.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "slwsubg.mm"
include "syl.mm"
include "simpl2.mm"
include "slwhash.mm"
include "jca.mm"
include "cv.mm"
include "wss.mm"
include "cress.mm"
include "cpgp.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "simpl3.mm"
include "simprl.mm"
include "cen.mm"
include "adantr.mm"
include "subgss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "simprrl.mm"
include "cdom.mm"
include "ssdomg.mm"
include "sylc.mm"
include "cle.mm"
include "cn.mm"
include "cbs.mm"
include "cn0.mm"
include "wrex.mm"
include "simprrr.mm"
include "eqid.mm"
include "subggrp.mm"
include "subgbas.mm"
include "eqeltrrd.mm"
include "pgpfi.mm"
include "mpbid.mm"
include "simpld.mm"
include "prmnn.mm"
include "nnred.mm"
include "nnge1d.mm"
include "cz.mm"
include "cuz.mm"
include "c0.mm"
include "wne.mm"
include "c0g.mm"
include "subg0cl.mm"
include "ne0i.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "pccld.mm"
include "nn0zd.mm"
include "simpl1.mm"
include "grpbn0.mm"
include "cdvds.mm"
include "lagsubg.mm"
include "nnzd.mm"
include "pc2dvds.mm"
include "oveq1.mm"
include "breq12d.mm"
include "rspcv.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "leexp2ad.mm"
include "simprd.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "pcprmpw.mm"
include "simplrr.mm"
include "3brtr4d.mm"
include "ad2antrl.mm"
include "hashdom.mm"
include "sbth.mm"
include "fisseneq.mm"
include "syl3anc.mm"
include "expr.mm"
include "simprr.mm"
include "eqtr3d.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpbir2and.mm"
include "breq2d.mm"
include "eqimss.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "syl5ibcom.mm"
include "impbid.mm"
include "ralrimiva.mm"
include "isslw.mm"
include "impbida.mm"

theorem fislw
  let cP: class P
  let cG: class G
  let cH: class H
  let cX: class X
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vp: setvar p
  let wph: wff ph
  assume fislw.1: |- X = ( Base ` G )


  assert |- ( ( G e. Grp /\ X e. Fin /\ P e. Prime ) -> ( H e. ( P pSyl G ) <-> ( H e. ( SubGrp ` G ) /\ ( # ` H ) = ( P ^ ( P pCnt ( # ` X ) ) ) ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cfn
    wcel
    #
    cP
    cprime
    wcel
    #
    w3a
    #
    cH
    cP
    cG
    cslw
    co
    wcel
    #
    cH
    cG
    csubg
    cfv
    #
    wcel
    #
    cH
    chash
    cfv
    #
    cP
    cP
    cX
    chash
    cfv
    #
    cpc
    co
    #
    cexp
    co
    #
    wceq
    #
    wa
    #
    @3
    @4
    wa
    #
    @6
    @11
    @13
    @4
    @6
    @3
    @4
    simpr
    #
    cP
    cG
    cH
    slwsubg
    syl
    @13
    cP
    cG
    cH
    cX
    fislw.1
    @0
    @1
    @2
    @4
    simpl2
    @14
    slwhash
    jca
    @3
    @12
    wa
    #
    @2
    @6
    cH
    vk
    cv
    #
    wss
    #
    cP
    cG
    @16
    cress
    co
    #
    cpgp
    wbr
    #
    wa
    #
    cH
    @16
    wceq
    #
    wb
    #
    vk
    @5
    wral
    @4
    @0
    @1
    @2
    @12
    simpl3
    #
    @3
    @6
    @11
    simprl
    @15
    @22
    vk
    @5
    @15
    @16
    @5
    wcel
    #
    wa
    #
    @20
    @21
    @15
    @24
    @20
    @21
    @15
    @24
    @20
    wa
    #
    wa
    #
    @16
    cfn
    wcel
    #
    @17
    cH
    @16
    cen
    wbr
    #
    @21
    @27
    @1
    @16
    cX
    wss
    #
    @28
    @15
    @1
    @26
    @0
    @1
    @2
    @12
    simpl2
    #
    adantr
    #
    @27
    @24
    @30
    @15
    @24
    @20
    simprl
    #
    cX
    @16
    cG
    fislw.1
    subgss
    syl
    cX
    @16
    ssfi
    syl2anc
    #
    @15
    @24
    @17
    @19
    simprrl
    #
    @27
    cH
    @16
    cdom
    wbr
    #
    @16
    cH
    cdom
    wbr
    #
    @29
    @27
    @28
    @17
    @36
    @34
    @35
    cH
    @16
    cfn
    ssdomg
    sylc
    @27
    @16
    chash
    cfv
    #
    @7
    cle
    wbr
    #
    @37
    @27
    cP
    cP
    @38
    cpc
    co
    #
    cexp
    co
    #
    @10
    @38
    @7
    cle
    @27
    cP
    @40
    @9
    @27
    cP
    @27
    @2
    cP
    cn
    wcel
    @27
    @2
    @18
    cbs
    cfv
    #
    chash
    cfv
    #
    cP
    vn
    cv
    #
    cexp
    co
    #
    wceq
    #
    vn
    cn0
    wrex
    #
    @27
    @19
    @2
    @47
    wa
    #
    @15
    @24
    @17
    @19
    simprrr
    @27
    @18
    cgrp
    wcel
    #
    @42
    cfn
    wcel
    @19
    @48
    wb
    @27
    @24
    @49
    @33
    @16
    cG
    @18
    @18
    eqid
    #
    subggrp
    syl
    @27
    @16
    @42
    cfn
    @27
    @24
    @16
    @42
    wceq
    @33
    @16
    cG
    @18
    @50
    subgbas
    syl
    #
    @34
    eqeltrrd
    cP
    vn
    @18
    @42
    @42
    eqid
    pgpfi
    syl2anc
    mpbid
    #
    simpld
    #
    cP
    prmnn
    syl
    #
    nnred
    @27
    cP
    @54
    nnge1d
    @27
    @40
    cz
    wcel
    @9
    cz
    wcel
    @40
    @9
    cle
    wbr
    #
    @9
    @40
    cuz
    cfv
    wcel
    @27
    @40
    @27
    cP
    @38
    @53
    @27
    @38
    cn
    wcel
    #
    @16
    c0
    wne
    #
    @27
    cG
    c0g
    cfv
    #
    @16
    wcel
    #
    @57
    @27
    @24
    @59
    @33
    @16
    cG
    @58
    @58
    eqid
    subg0cl
    syl
    @16
    @58
    ne0i
    syl
    @27
    @28
    @56
    @57
    wb
    @34
    @16
    hashnncl
    syl
    mpbird
    #
    pccld
    nn0zd
    @27
    @9
    @15
    @9
    cn0
    wcel
    #
    @26
    @15
    cP
    @8
    @23
    @15
    @8
    cn
    wcel
    #
    cX
    c0
    wne
    #
    @15
    @0
    @63
    @0
    @1
    @2
    @12
    simpl1
    cX
    cG
    fislw.1
    grpbn0
    syl
    @15
    @1
    @62
    @63
    wb
    @31
    cX
    hashnncl
    syl
    mpbird
    #
    pccld
    #
    adantr
    nn0zd
    @27
    @2
    vp
    cv
    #
    @38
    cpc
    co
    #
    @66
    @8
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
    @55
    @53
    @27
    @38
    @8
    cdvds
    wbr
    #
    @70
    @27
    @24
    @1
    @71
    @33
    @32
    cG
    cX
    @16
    fislw.1
    lagsubg
    syl2anc
    @27
    @38
    cz
    wcel
    @8
    cz
    wcel
    @71
    @70
    wb
    @27
    @38
    @60
    nnzd
    @27
    @8
    @15
    @62
    @26
    @64
    adantr
    nnzd
    @38
    @8
    vp
    pc2dvds
    syl2anc
    mpbid
    @69
    @55
    vp
    cP
    cprime
    @66
    cP
    wceq
    @67
    @40
    @68
    @9
    cle
    @66
    cP
    @38
    cpc
    oveq1
    @66
    cP
    @8
    cpc
    oveq1
    breq12d
    rspcv
    sylc
    @40
    @9
    eluz2
    syl3anbrc
    leexp2ad
    @27
    @38
    @45
    wceq
    #
    vn
    cn0
    wrex
    #
    @38
    @41
    wceq
    #
    @27
    @73
    @47
    @27
    @2
    @47
    @52
    simprd
    @27
    @72
    @46
    vn
    cn0
    @27
    @38
    @43
    @45
    @27
    @16
    @42
    chash
    @51
    fveq2d
    eqeq1d
    rexbidv
    mpbird
    @27
    @2
    @56
    @73
    @74
    wb
    @53
    @60
    @38
    cP
    vn
    pcprmpw
    syl2anc
    mpbid
    @3
    @6
    @11
    @26
    simplrr
    3brtr4d
    @27
    @28
    cH
    cfn
    wcel
    #
    @39
    @37
    wb
    @34
    @15
    @75
    @26
    @15
    @1
    cH
    cX
    wss
    #
    @75
    @31
    @6
    @76
    @3
    @11
    cX
    cH
    cG
    fislw.1
    subgss
    ad2antrl
    cX
    cH
    ssfi
    syl2anc
    #
    adantr
    @16
    cH
    cfn
    hashdom
    syl2anc
    mpbid
    cH
    @16
    sbth
    syl2anc
    cH
    @16
    fisseneq
    syl3anc
    expr
    @25
    cP
    cG
    cH
    cress
    co
    #
    cpgp
    wbr
    #
    @21
    @20
    @15
    @79
    @24
    @15
    @79
    @2
    @78
    cbs
    cfv
    #
    chash
    cfv
    #
    @45
    wceq
    #
    vn
    cn0
    wrex
    #
    @23
    @15
    @61
    @81
    @10
    wceq
    #
    @83
    @65
    @15
    @7
    @81
    @10
    @15
    cH
    @80
    chash
    @6
    cH
    @80
    wceq
    @3
    @11
    cH
    cG
    @78
    @78
    eqid
    #
    subgbas
    ad2antrl
    #
    fveq2d
    @3
    @6
    @11
    simprr
    eqtr3d
    @82
    @84
    vn
    @9
    cn0
    @44
    @9
    wceq
    @45
    @10
    @81
    @44
    @9
    cP
    cexp
    oveq2
    eqeq2d
    rspcev
    syl2anc
    @15
    @78
    cgrp
    wcel
    #
    @80
    cfn
    wcel
    @79
    @2
    @83
    wa
    wb
    @6
    @87
    @3
    @11
    cH
    cG
    @78
    @85
    subggrp
    ad2antrl
    @15
    cH
    @80
    cfn
    @86
    @77
    eqeltrrd
    cP
    vn
    @78
    @80
    @80
    eqid
    pgpfi
    syl2anc
    mpbir2and
    adantr
    @21
    @79
    @19
    @20
    @21
    @78
    @18
    cP
    cpgp
    cH
    @16
    cG
    cress
    oveq2
    breq2d
    @21
    @17
    @19
    cH
    @16
    eqimss
    biantrurd
    bitrd
    syl5ibcom
    impbid
    ralrimiva
    cP
    vk
    cG
    cH
    isslw
    syl3anbrc
    impbida
end
