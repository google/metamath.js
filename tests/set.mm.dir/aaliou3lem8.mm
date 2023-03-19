include "cn.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "cfa.mm"
include "cfv.mm"
include "cneg.mm"
include "cmul.mm"
include "cle.mm"
include "wrex.mm"
include "cr.mm"
include "2rp.mm"
include "rpdivcl.mm"
include "mpan.mm"
include "rpred.mm"
include "2re.mm"
include "1lt2.mm"
include "expnbnd.mm"
include "mp3an23.mm"
include "syl.mm"
include "adantl.mm"
include "cmin.mm"
include "simprl.mm"
include "simpll.mm"
include "nnaddm1cl.mm"
include "syl2anc.mm"
include "simplr.mm"
include "rerpdivcl.mm"
include "sylancr.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "reexpcl.mm"
include "cz.mm"
include "nnaddcld.mm"
include "nnm1nn0.mm"
include "peano2nn0.mm"
include "faccl.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "zsubcld.mm"
include "rpexpcl.mm"
include "simprr.mm"
include "ltled.mm"
include "a1i.mm"
include "1le2.mm"
include "cuz.mm"
include "nnred.mm"
include "nn0ge0d.mm"
include "nnge1d.mm"
include "lemulge12d.mm"
include "wceq.mm"
include "facp1.mm"
include "oveq1d.mm"
include "nncnd.mm"
include "nn0cnd.mm"
include "subdid.mm"
include "1cnd.mm"
include "npcand.mm"
include "pncand.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtr2d.mm"
include "breqtrrd.mm"
include "wb.mm"
include "eluz.mm"
include "mpbird.mm"
include "leexp2ad.mm"
include "letrd.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "rpcnne0.mm"
include "mp1i.mm"
include "expsub.mm"
include "syl12anc.mm"
include "2cn.mm"
include "expmuld.mm"
include "rpcnd.mm"
include "rpexpcld.mm"
include "rpne0d.mm"
include "divrecd.mm"
include "3eqtrrd.mm"
include "rpreccld.mm"
include "rpmulcld.mm"
include "ledivmuld.mm"
include "mpbid.mm"
include "mul12d.mm"
include "breqtrd.mm"
include "expneg.mm"
include "eqtr4d.mm"
include "3brtr4d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "negeqd.mm"
include "fveq2.mm"
include "breq12d.mm"
include "rspcev.mm"
include "rexlimddv.mm"

theorem aaliou3lem8
  let vx: setvar x
  let cA: class A
  let cB: class B
  let va: setvar a

  disjoint A x
  disjoint B x
  disjoint A a
  disjoint a x
  disjoint B a
  assert |- ( ( A e. NN /\ B e. RR+ ) -> E. x e. NN ( 2 x. ( 2 ^ -u ( ! ` ( x + 1 ) ) ) ) <_ ( B / ( ( 2 ^ ( ! ` x ) ) ^ A ) ) )

  proof
    cA
    cn
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    c2
    cB
    cdiv
    co
    #
    c2
    va
    cv
    #
    cexp
    co
    #
    clt
    wbr
    #
    c2
    c2
    vx
    cv
    #
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    cmul
    co
    #
    cB
    c2
    @7
    cfa
    cfv
    #
    cexp
    co
    #
    cA
    cexp
    co
    #
    cdiv
    co
    #
    cle
    wbr
    #
    vx
    cn
    wrex
    #
    va
    cn
    @1
    @6
    va
    cn
    wrex
    #
    @0
    @1
    @3
    cr
    wcel
    #
    @19
    @1
    @3
    c2
    crp
    wcel
    #
    @1
    @3
    crp
    wcel
    2rp
    c2
    cB
    rpdivcl
    mpan
    rpred
    @20
    c2
    cr
    wcel
    #
    c1
    c2
    clt
    wbr
    @19
    2re
    1lt2
    @3
    c2
    va
    expnbnd
    mp3an23
    syl
    adantl
    @2
    @4
    cn
    wcel
    #
    @6
    wa
    #
    wa
    #
    @4
    cA
    caddc
    co
    #
    c1
    cmin
    co
    #
    cn
    wcel
    #
    c2
    c2
    @27
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    cmul
    co
    #
    cB
    c2
    @27
    cfa
    cfv
    #
    cexp
    co
    #
    cA
    cexp
    co
    #
    cdiv
    co
    #
    cle
    wbr
    #
    @18
    @25
    @23
    @0
    @28
    @2
    @23
    @6
    simprl
    #
    @0
    @1
    @24
    simpll
    #
    @4
    cA
    nnaddm1cl
    syl2anc
    @25
    c2
    c2
    @30
    cexp
    co
    #
    cdiv
    co
    #
    cB
    c1
    @36
    cdiv
    co
    #
    cmul
    co
    #
    @33
    @37
    cle
    @25
    @42
    @44
    cle
    wbr
    c2
    @41
    @44
    cmul
    co
    #
    cle
    wbr
    @25
    c2
    cB
    @41
    @43
    cmul
    co
    #
    cmul
    co
    #
    @45
    cle
    @25
    @3
    @46
    cle
    wbr
    c2
    @47
    cle
    wbr
    @25
    @3
    c2
    @30
    @34
    cA
    cmul
    co
    #
    cmin
    co
    #
    cexp
    co
    #
    @46
    cle
    @25
    @3
    @5
    @50
    @25
    @22
    @1
    @20
    2re
    @0
    @1
    @24
    simplr
    #
    c2
    cB
    rerpdivcl
    sylancr
    #
    @25
    @22
    @4
    cn0
    wcel
    @5
    cr
    wcel
    2re
    @25
    @4
    @39
    nnnn0d
    #
    c2
    @4
    reexpcl
    sylancr
    #
    @25
    @50
    @25
    @21
    @49
    cz
    wcel
    #
    @50
    crp
    wcel
    2rp
    @25
    @30
    @48
    @25
    @30
    @25
    @29
    cn0
    wcel
    #
    @30
    cn
    wcel
    @25
    @27
    cn0
    wcel
    #
    @56
    @25
    @26
    cn
    wcel
    @57
    @25
    @4
    cA
    @39
    @40
    nnaddcld
    #
    @26
    nnm1nn0
    syl
    #
    @27
    peano2nn0
    syl
    #
    @29
    faccl
    syl
    #
    nnzd
    #
    @25
    @34
    cA
    @25
    @34
    @25
    @57
    @34
    cn
    wcel
    @59
    @27
    faccl
    syl
    #
    nnzd
    #
    @25
    cA
    @40
    nnzd
    #
    zmulcld
    #
    zsubcld
    #
    c2
    @49
    rpexpcl
    sylancr
    rpred
    @25
    @3
    @5
    @52
    @54
    @2
    @23
    @6
    simprr
    ltled
    @25
    c2
    @4
    @49
    @22
    @25
    2re
    a1i
    #
    c1
    c2
    cle
    wbr
    @25
    1le2
    a1i
    @25
    @49
    @4
    cuz
    cfv
    wcel
    #
    @4
    @49
    cle
    wbr
    #
    @25
    @4
    @34
    @4
    cmul
    co
    #
    @49
    cle
    @25
    @4
    @34
    @25
    @4
    @39
    nnred
    @25
    @34
    @63
    nnred
    @25
    @4
    @53
    nn0ge0d
    @25
    @34
    @63
    nnge1d
    lemulge12d
    @25
    @49
    @34
    @29
    cmul
    co
    #
    @48
    cmin
    co
    @34
    @29
    cA
    cmin
    co
    #
    cmul
    co
    @71
    @25
    @30
    @72
    @48
    cmin
    @25
    @57
    @30
    @72
    wceq
    @59
    @27
    facp1
    syl
    oveq1d
    @25
    @34
    @29
    cA
    @25
    @34
    @63
    nncnd
    @25
    @29
    @60
    nn0cnd
    @25
    cA
    @40
    nncnd
    #
    subdid
    @25
    @73
    @4
    @34
    cmul
    @25
    @73
    @26
    cA
    cmin
    co
    @4
    @25
    @29
    @26
    cA
    cmin
    @25
    @26
    c1
    @25
    @26
    @58
    nncnd
    @25
    1cnd
    npcand
    oveq1d
    @25
    @4
    cA
    @25
    @4
    @39
    nncnd
    @74
    pncand
    eqtrd
    oveq2d
    3eqtr2d
    breqtrrd
    @25
    @4
    cz
    wcel
    @55
    @69
    @70
    wb
    @25
    @4
    @39
    nnzd
    @67
    @4
    @49
    eluz
    syl2anc
    mpbird
    leexp2ad
    letrd
    @25
    @50
    @41
    c2
    @48
    cexp
    co
    #
    cdiv
    co
    #
    @41
    @36
    cdiv
    co
    @46
    @25
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    wa
    #
    @30
    cz
    wcel
    #
    @48
    cz
    wcel
    @50
    @76
    wceq
    @21
    @78
    @25
    2rp
    c2
    rpcnne0
    mp1i
    @62
    @66
    c2
    @30
    @48
    expsub
    syl12anc
    @25
    @75
    @36
    @41
    cdiv
    @25
    c2
    @34
    cA
    @77
    @25
    2cn
    a1i
    #
    @25
    cA
    @40
    nnnn0d
    @25
    @34
    @63
    nnnn0d
    expmuld
    oveq2d
    @25
    @41
    @36
    @25
    @41
    @25
    @21
    @79
    @41
    crp
    wcel
    2rp
    @62
    c2
    @30
    rpexpcl
    sylancr
    #
    rpcnd
    #
    @25
    @36
    @25
    @35
    cA
    @25
    @21
    @34
    cz
    wcel
    @35
    crp
    wcel
    2rp
    @64
    c2
    @34
    rpexpcl
    sylancr
    @65
    rpexpcld
    #
    rpcnd
    #
    @25
    @36
    @83
    rpne0d
    #
    divrecd
    3eqtrrd
    breqtrrd
    @25
    c2
    @46
    cB
    @68
    @25
    @46
    @25
    @41
    @43
    @81
    @25
    @36
    @83
    rpreccld
    #
    rpmulcld
    rpred
    @51
    ledivmuld
    mpbid
    @25
    cB
    @41
    @43
    @25
    cB
    @51
    rpcnd
    #
    @82
    @25
    @43
    @86
    rpcnd
    mul12d
    breqtrd
    @25
    c2
    @44
    @41
    @68
    @25
    @44
    @25
    cB
    @43
    @51
    @86
    rpmulcld
    rpred
    @81
    ledivmuld
    mpbird
    @25
    @33
    c2
    c1
    @41
    cdiv
    co
    #
    cmul
    co
    @42
    @25
    @32
    @88
    c2
    cmul
    @25
    @77
    @30
    cn0
    wcel
    @32
    @88
    wceq
    2cn
    @25
    @30
    @61
    nnnn0d
    c2
    @30
    expneg
    sylancr
    oveq2d
    @25
    c2
    @41
    @80
    @82
    @25
    @41
    @81
    rpne0d
    divrecd
    eqtr4d
    @25
    cB
    @36
    @87
    @84
    @85
    divrecd
    3brtr4d
    @17
    @38
    vx
    @27
    cn
    @7
    @27
    wceq
    #
    @12
    @33
    @16
    @37
    cle
    @89
    @11
    @32
    c2
    cmul
    @89
    @10
    @31
    c2
    cexp
    @89
    @9
    @30
    @89
    @8
    @29
    cfa
    @7
    @27
    c1
    caddc
    oveq1
    fveq2d
    negeqd
    oveq2d
    oveq2d
    @89
    @15
    @36
    cB
    cdiv
    @89
    @14
    @35
    cA
    cexp
    @89
    @13
    @34
    c2
    cexp
    @7
    @27
    cfa
    fveq2
    oveq2d
    oveq1d
    oveq2d
    breq12d
    rspcev
    syl2anc
    rexlimddv
end
