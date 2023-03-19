include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cdom.mm"
include "wb.mm"
include "ccrd.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "com.mm"
include "wrex.mm"
include "wss.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "fzfi.mm"
include "ficardom.mm"
include "ax-mp.mm"
include "cvv.mm"
include "caddc.mm"
include "cmpt.mm"
include "cc0.mm"
include "crdg.mm"
include "cres.mm"
include "ccnv.mm"
include "eqid.mm"
include "hashgval.mm"
include "ad2antrr.mm"
include "cn0.mm"
include "hashcl.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "nn0sub2.mm"
include "syl3anc.mm"
include "hashfz1.mm"
include "syl.mm"
include "syl5eq.mm"
include "oveq12d.mm"
include "cc.mm"
include "nn0cnd.mm"
include "pncan3.mm"
include "syl2an.mm"
include "adantr.mm"
include "eqtrd.mm"
include "hashgadd.mm"
include "sylancl.mm"
include "3eqtr4d.mm"
include "fveq2d.mm"
include "wf1o.mm"
include "hashgf1o.mm"
include "nnacl.mm"
include "f1ocnvfv1.mm"
include "sylancr.mm"
include "3eqtr3d.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "ex.mm"
include "cardnn.mm"
include "adantl.mm"
include "oveq2d.mm"
include "fveq2.mm"
include "wi.mm"
include "nnfi.mm"
include "oveqan12d.mm"
include "adantlr.mm"
include "eqeq12d.mm"
include "nn0ge0d.mm"
include "cr.mm"
include "nn0red.mm"
include "addge01.mm"
include "mpbid.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "sylbid.mm"
include "sylan2.mm"
include "syl5.mm"
include "sylbird.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "nnawordex.mm"
include "cdm.mm"
include "finnum.mm"
include "carddom2.mm"
include "3bitr2d.mm"
include "wn.mm"
include "cpnf.mm"
include "cxr.mm"
include "hashxrcl.mm"
include "pnfge.mm"
include "hashinf.mm"
include "adantll.mm"
include "breqtrrd.mm"
include "wf1.mm"
include "wex.mm"
include "isinffi.mm"
include "ancoms.mm"
include "brdomg.mm"
include "mpbird.mm"
include "2thd.mm"
include "pm2.61dan.mm"

theorem hashdom
  let cA: class A
  let cB: class B
  let cV: class V
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. Fin /\ B e. V ) -> ( ( # ` A ) <_ ( # ` B ) <-> A ~<_ B ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    cB
    cfn
    wcel
    #
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    cle
    wbr
    #
    cA
    cB
    cdom
    wbr
    #
    wb
    #
    @0
    @3
    @8
    @1
    @0
    @3
    wa
    #
    @6
    cA
    ccrd
    cfv
    #
    vy
    cv
    #
    coa
    co
    #
    cB
    ccrd
    cfv
    #
    wceq
    #
    vy
    com
    wrex
    #
    @10
    @13
    wss
    #
    @7
    @9
    @6
    @15
    @9
    @6
    @15
    @9
    @6
    wa
    #
    c1
    @5
    @4
    cmin
    co
    #
    cfz
    co
    #
    ccrd
    cfv
    #
    com
    wcel
    #
    @10
    @20
    coa
    co
    #
    @13
    wceq
    #
    @15
    @19
    cfn
    wcel
    #
    @21
    c1
    @18
    fzfi
    #
    @19
    ficardom
    ax-mp
    #
    @17
    @22
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    cc0
    crdg
    com
    cres
    #
    cfv
    #
    @27
    ccnv
    #
    cfv
    #
    @13
    @27
    cfv
    #
    @29
    cfv
    #
    @22
    @13
    @17
    @28
    @31
    @29
    @17
    @10
    @27
    cfv
    #
    @20
    @27
    cfv
    #
    caddc
    co
    #
    @5
    @28
    @31
    @17
    @35
    @4
    @18
    caddc
    co
    #
    @5
    @17
    @33
    @4
    @34
    @18
    caddc
    @0
    @33
    @4
    wceq
    @3
    @6
    vx
    cA
    @27
    @27
    eqid
    #
    hashgval
    #
    ad2antrr
    @17
    @34
    @19
    chash
    cfv
    #
    @18
    @24
    @34
    @39
    wceq
    @25
    vx
    @19
    @27
    @37
    hashgval
    ax-mp
    @17
    @18
    cn0
    wcel
    #
    @39
    @18
    wceq
    @17
    @4
    cn0
    wcel
    #
    @5
    cn0
    wcel
    #
    @6
    @40
    @0
    @41
    @3
    @6
    cA
    hashcl
    #
    ad2antrr
    @3
    @42
    @0
    @6
    cB
    hashcl
    #
    ad2antlr
    @9
    @6
    simpr
    @4
    @5
    nn0sub2
    syl3anc
    @18
    hashfz1
    syl
    syl5eq
    oveq12d
    @9
    @36
    @5
    wceq
    #
    @6
    @0
    @4
    cc
    wcel
    @5
    cc
    wcel
    @45
    @3
    @0
    @4
    @43
    nn0cnd
    @3
    @5
    @44
    nn0cnd
    @4
    @5
    pncan3
    syl2an
    adantr
    eqtrd
    @17
    @10
    com
    wcel
    #
    @21
    @28
    @35
    wceq
    @0
    @46
    @3
    @6
    cA
    ficardom
    #
    ad2antrr
    #
    @26
    vx
    @10
    @20
    @27
    @37
    hashgadd
    sylancl
    @3
    @31
    @5
    wceq
    #
    @0
    @6
    vx
    cB
    @27
    @37
    hashgval
    #
    ad2antlr
    3eqtr4d
    fveq2d
    @17
    com
    cn0
    @27
    wf1o
    #
    @22
    com
    wcel
    #
    @30
    @22
    wceq
    vx
    @27
    @37
    hashgf1o
    #
    @17
    @46
    @21
    @52
    @48
    @26
    @10
    @20
    nnacl
    sylancl
    com
    cn0
    @22
    @27
    f1ocnvfv1
    sylancr
    @17
    @51
    @13
    com
    wcel
    #
    @32
    @13
    wceq
    @53
    @3
    @54
    @0
    @6
    cB
    ficardom
    #
    ad2antlr
    com
    cn0
    @13
    @27
    f1ocnvfv1
    sylancr
    3eqtr3d
    @14
    @23
    vy
    @20
    com
    @11
    @20
    wceq
    @12
    @22
    @13
    @11
    @20
    @10
    coa
    oveq2
    eqeq1d
    rspcev
    sylancr
    ex
    @9
    @14
    @6
    vy
    com
    @9
    @11
    com
    wcel
    #
    wa
    #
    @14
    @10
    @11
    ccrd
    cfv
    #
    coa
    co
    #
    @13
    wceq
    #
    @6
    @57
    @59
    @12
    @13
    @57
    @58
    @11
    @10
    coa
    @56
    @58
    @11
    wceq
    @9
    @11
    cardnn
    adantl
    oveq2d
    eqeq1d
    @60
    @59
    @27
    cfv
    #
    @31
    wceq
    #
    @57
    @6
    @59
    @13
    @27
    fveq2
    @56
    @9
    @11
    cfn
    wcel
    #
    @62
    @6
    wi
    @11
    nnfi
    @9
    @63
    wa
    #
    @62
    @4
    @11
    chash
    cfv
    #
    caddc
    co
    #
    @5
    wceq
    #
    @6
    @64
    @61
    @66
    @31
    @5
    @0
    @63
    @61
    @66
    wceq
    @3
    @0
    @63
    wa
    #
    @61
    @33
    @58
    @27
    cfv
    #
    caddc
    co
    #
    @66
    @0
    @46
    @58
    com
    wcel
    @61
    @70
    wceq
    @63
    @47
    @11
    ficardom
    vx
    @10
    @58
    @27
    @37
    hashgadd
    syl2an
    @0
    @63
    @33
    @4
    @69
    @65
    caddc
    @38
    vx
    @11
    @27
    @37
    hashgval
    oveqan12d
    eqtrd
    adantlr
    @3
    @49
    @0
    @63
    @50
    ad2antlr
    eqeq12d
    @64
    @4
    @66
    cle
    wbr
    #
    @67
    @6
    @0
    @63
    @71
    @3
    @68
    cc0
    @65
    cle
    wbr
    #
    @71
    @63
    @72
    @0
    @63
    @65
    @11
    hashcl
    #
    nn0ge0d
    adantl
    @0
    @4
    cr
    wcel
    @65
    cr
    wcel
    @72
    @71
    wb
    @63
    @0
    @4
    @43
    nn0red
    @63
    @65
    @73
    nn0red
    @4
    @65
    addge01
    syl2an
    mpbid
    adantlr
    @66
    @5
    @4
    cle
    breq2
    syl5ibcom
    sylbid
    sylan2
    syl5
    sylbird
    rexlimdva
    impbid
    @0
    @46
    @54
    @16
    @15
    wb
    @3
    @47
    @55
    vy
    @10
    @13
    nnawordex
    syl2an
    @0
    cA
    ccrd
    cdm
    #
    wcel
    cB
    @74
    wcel
    @16
    @7
    wb
    @3
    cA
    finnum
    cB
    finnum
    cA
    cB
    carddom2
    syl2an
    3bitr2d
    adantlr
    @2
    @3
    wn
    #
    wa
    #
    @6
    @7
    @76
    @4
    cpnf
    @5
    cle
    @76
    @4
    cxr
    wcel
    #
    @4
    cpnf
    cle
    wbr
    @0
    @77
    @1
    @75
    cA
    cfn
    hashxrcl
    ad2antrr
    @4
    pnfge
    syl
    @1
    @75
    @5
    cpnf
    wceq
    @0
    cB
    cV
    hashinf
    adantll
    breqtrrd
    @76
    @7
    cA
    cB
    vf
    cv
    wf1
    vf
    wex
    #
    @0
    @75
    @78
    @1
    @75
    @0
    @78
    cB
    cA
    vf
    isinffi
    ancoms
    adantlr
    @1
    @7
    @78
    wb
    @0
    @75
    cA
    cB
    cV
    vf
    brdomg
    ad2antlr
    mpbird
    2thd
    pm2.61dan
end
