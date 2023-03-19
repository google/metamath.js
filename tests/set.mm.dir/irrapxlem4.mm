include "crp.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "cdiv.mm"
include "cfl.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "clt.mm"
include "wrex.mm"
include "cfz.mm"
include "cn0.mm"
include "elfznn.mm"
include "ad3antlr.mm"
include "cz.mm"
include "cc0.mm"
include "nn0z.mm"
include "ad2antlr.mm"
include "cneg.mm"
include "simpl.mm"
include "ad3antrrr.mm"
include "rpred.mm"
include "nnred.mm"
include "remulcld.mm"
include "cr.mm"
include "nn0re.mm"
include "resubcld.mm"
include "recnd.mm"
include "abscld.mm"
include "rpreccld.mm"
include "rprege0d.mm"
include "flge0nn0.mm"
include "nn0p1nn.mm"
include "3syl.mm"
include "simpr.mm"
include "ifcld.mm"
include "nnrecred.mm"
include "0red.mm"
include "rprecred.mm"
include "flcld.mm"
include "zred.mm"
include "peano2re.mm"
include "syl.mm"
include "max2.mm"
include "syl2anc.mm"
include "wb.mm"
include "nngt0d.mm"
include "lerec.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "fllep1.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "recrecd.mm"
include "breqtrrd.mm"
include "recgt0d.mm"
include "rpgt0d.mm"
include "mpbird.mm"
include "letrd.mm"
include "mulid1d.mm"
include "nnge1d.mm"
include "1red.mm"
include "lemul2d.mm"
include "eqbrtrrd.mm"
include "subid1d.mm"
include "ltletrd.mm"
include "absltd.mm"
include "simprd.mm"
include "ltsub2d.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "elfzle2.mm"
include "max1.mm"
include "maxle.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1.mm"
include "id.mm"
include "ifbieq2d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "breq1d.mm"
include "rspc2ev.mm"
include "irrapxlem3.mm"
include "r19.29vva.mm"

theorem irrapxlem4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint a y
  disjoint b y
  disjoint B a
  disjoint B b
  assert |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. NN E. y e. NN ( abs ` ( ( A x. x ) - y ) ) < ( 1 / if ( x <_ B , B , x ) ) )

  proof
    cA
    crp
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    cA
    va
    cv
    #
    cmul
    co
    #
    vb
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    cB
    c1
    cA
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @10
    cB
    cif
    #
    cdiv
    co
    #
    clt
    wbr
    #
    cA
    vx
    cv
    #
    cmul
    co
    #
    vy
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    @15
    cB
    cle
    wbr
    #
    cB
    @15
    cif
    #
    cdiv
    co
    #
    clt
    wbr
    #
    vy
    cn
    wrex
    vx
    cn
    wrex
    #
    va
    vb
    c1
    @12
    cfz
    co
    #
    cn0
    @2
    @3
    @25
    wcel
    #
    wa
    #
    @5
    cn0
    wcel
    #
    wa
    #
    @14
    wa
    #
    @3
    cn
    wcel
    #
    @5
    cn
    wcel
    #
    @7
    c1
    @3
    cB
    cle
    wbr
    #
    cB
    @3
    cif
    #
    cdiv
    co
    #
    clt
    wbr
    #
    @24
    @26
    @31
    @2
    @28
    @14
    @3
    @12
    elfznn
    ad3antlr
    #
    @30
    @5
    cz
    wcel
    #
    cc0
    @5
    clt
    wbr
    #
    @32
    @28
    @38
    @27
    @14
    @5
    nn0z
    ad2antlr
    @30
    @39
    @6
    @4
    cc0
    cmin
    co
    #
    clt
    wbr
    #
    @30
    @40
    cneg
    @6
    clt
    wbr
    #
    @41
    @30
    @7
    @40
    clt
    wbr
    @42
    @41
    wa
    @30
    @7
    @13
    @40
    @30
    @6
    @30
    @6
    @30
    @4
    @5
    @30
    cA
    @3
    @30
    cA
    @2
    @0
    @26
    @28
    @14
    @0
    @1
    simpl
    #
    ad3antrrr
    #
    rpred
    #
    @30
    @3
    @37
    nnred
    #
    remulcld
    #
    @28
    @5
    cr
    wcel
    @27
    @14
    @5
    nn0re
    ad2antlr
    #
    resubcld
    #
    recnd
    abscld
    #
    @30
    @12
    @30
    @11
    @10
    cB
    cn
    @2
    @10
    cn
    wcel
    #
    @26
    @28
    @14
    @2
    @8
    cr
    wcel
    #
    cc0
    @8
    cle
    wbr
    wa
    @9
    cn0
    wcel
    @51
    @2
    @8
    @2
    cA
    @43
    rpreccld
    rprege0d
    @8
    flge0nn0
    @9
    nn0p1nn
    3syl
    #
    ad3antrrr
    #
    @2
    @1
    @26
    @28
    @14
    @0
    @1
    simpr
    #
    ad3antrrr
    #
    ifcld
    #
    nnrecred
    #
    @30
    @4
    cc0
    @47
    @30
    0red
    #
    resubcld
    #
    @29
    @14
    simpr
    #
    @30
    @13
    cA
    @40
    @58
    @45
    @60
    @30
    @13
    c1
    @10
    cdiv
    co
    #
    cA
    @58
    @30
    @10
    @54
    nnrecred
    #
    @45
    @30
    @10
    @12
    cle
    wbr
    #
    @13
    @62
    cle
    wbr
    #
    @30
    cB
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    @64
    @30
    cB
    @56
    nnred
    #
    @30
    @9
    cr
    wcel
    @67
    @30
    @9
    @30
    @8
    @30
    cA
    @44
    rprecred
    #
    flcld
    zred
    @9
    peano2re
    syl
    #
    cB
    @10
    max2
    syl2anc
    @30
    @67
    cc0
    @10
    clt
    wbr
    @12
    cr
    wcel
    #
    cc0
    @12
    clt
    wbr
    #
    @64
    @65
    wb
    @70
    @30
    @10
    @54
    nngt0d
    #
    @30
    @12
    @57
    nnred
    #
    @30
    @12
    @57
    nngt0d
    #
    @10
    @12
    lerec
    syl22anc
    mpbid
    @30
    @62
    cA
    cle
    wbr
    #
    @8
    c1
    @62
    cdiv
    co
    #
    cle
    wbr
    #
    @30
    @8
    @10
    @77
    cle
    @30
    @52
    @8
    @10
    cle
    wbr
    @69
    @8
    fllep1
    syl
    @30
    @10
    @30
    @10
    @54
    nncnd
    @30
    @10
    @54
    nnne0d
    recrecd
    breqtrrd
    @30
    @62
    cr
    wcel
    cc0
    @62
    clt
    wbr
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    @76
    @78
    wb
    @63
    @30
    @10
    @70
    @73
    recgt0d
    @45
    @30
    cA
    @44
    rpgt0d
    @62
    cA
    lerec
    syl22anc
    mpbird
    letrd
    @30
    cA
    @4
    @40
    cle
    @30
    cA
    c1
    cmul
    co
    #
    cA
    @4
    cle
    @30
    cA
    @30
    cA
    @45
    recnd
    mulid1d
    @30
    c1
    @3
    cle
    wbr
    @79
    @4
    cle
    wbr
    @30
    @3
    @37
    nnge1d
    @30
    c1
    @3
    cA
    @30
    1red
    @46
    @44
    lemul2d
    mpbid
    eqbrtrrd
    @30
    @4
    @30
    @4
    @47
    recnd
    subid1d
    breqtrrd
    letrd
    ltletrd
    @30
    @6
    @40
    @49
    @60
    absltd
    mpbid
    simprd
    @30
    cc0
    @5
    @4
    @59
    @48
    @47
    ltsub2d
    mpbird
    @5
    elnnz
    sylanbrc
    @30
    @7
    @13
    @35
    @50
    @58
    @30
    @34
    @30
    @33
    cB
    @3
    cn
    @56
    @37
    ifcld
    nnrecred
    @61
    @30
    @34
    @12
    cle
    wbr
    #
    @13
    @35
    cle
    wbr
    #
    @30
    @80
    @3
    @12
    cle
    wbr
    #
    cB
    @12
    cle
    wbr
    #
    @26
    @82
    @2
    @28
    @14
    @3
    c1
    @12
    elfzle2
    ad3antlr
    @30
    @66
    @67
    @83
    @68
    @70
    cB
    @10
    max1
    syl2anc
    @30
    @3
    cr
    wcel
    #
    @66
    @71
    @80
    @82
    @83
    wa
    wb
    @46
    @68
    @74
    @3
    cB
    @12
    maxle
    syl3anc
    mpbir2and
    @30
    @34
    cr
    wcel
    cc0
    @34
    clt
    wbr
    @71
    @72
    @80
    @81
    wb
    @30
    @33
    cB
    @3
    cr
    @68
    @46
    ifcld
    #
    @30
    cc0
    cB
    @34
    @59
    @68
    @85
    @30
    cB
    @56
    nngt0d
    @30
    @84
    @66
    cB
    @34
    cle
    wbr
    @46
    @68
    @3
    cB
    max2
    syl2anc
    ltletrd
    @74
    @75
    @34
    @12
    lerec
    syl22anc
    mpbid
    ltletrd
    @23
    @36
    @4
    @17
    cmin
    co
    #
    cabs
    cfv
    #
    @35
    clt
    wbr
    vx
    vy
    @3
    @5
    cn
    cn
    vx
    va
    weq
    #
    @19
    @87
    @22
    @35
    clt
    @88
    @18
    @86
    cabs
    @88
    @16
    @4
    @17
    cmin
    @15
    @3
    cA
    cmul
    oveq2
    oveq1d
    fveq2d
    @88
    @21
    @34
    c1
    cdiv
    @88
    @20
    @33
    @15
    @3
    cB
    @15
    @3
    cB
    cle
    breq1
    @88
    id
    ifbieq2d
    oveq2d
    breq12d
    vy
    vb
    weq
    #
    @87
    @7
    @35
    clt
    @89
    @86
    @6
    cabs
    @17
    @5
    @4
    cmin
    oveq2
    fveq2d
    breq1d
    rspc2ev
    syl3anc
    @2
    @0
    @12
    cn
    wcel
    @14
    vb
    cn0
    wrex
    va
    @25
    wrex
    @43
    @2
    @11
    @10
    cB
    cn
    @53
    @55
    ifcld
    va
    vb
    cA
    @12
    irrapxlem3
    syl2anc
    r19.29vva
end
