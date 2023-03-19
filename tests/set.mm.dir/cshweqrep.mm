include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "cmo.mm"
include "cn0.mm"
include "wral.mm"
include "wi.mm"
include "c1.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "weq.mm"
include "zcn.mm"
include "mul02d.mm"
include "adantl.mm"
include "adantr.mm"
include "elfzoelz.mm"
include "zcnd.mm"
include "addid1d.mm"
include "ad2antll.mm"
include "eqtrd.mm"
include "zmodidfzoimp.mm"
include "eqtr2d.mm"
include "fveq1.mm"
include "eqcoms.mm"
include "ad2antrl.mm"
include "simprll.mm"
include "simprlr.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "elfzo0.mm"
include "nn0z.mm"
include "zmulcl.mm"
include "sylan.mm"
include "ancoms.mm"
include "zaddcl.mm"
include "syl2an.mm"
include "simplr.mm"
include "jca.mm"
include "ex.mm"
include "3adant3.mm"
include "sylbi.mm"
include "expd.mm"
include "com12.mm"
include "imp.mm"
include "impcom.mm"
include "zmodfzo.mm"
include "syl.mm"
include "cshwidxmod.mm"
include "syl3anc.mm"
include "cr.mm"
include "nn0re.mm"
include "zre.mm"
include "crp.mm"
include "nnrp.mm"
include "remulcl.mm"
include "readdcl.mm"
include "sylan2.mm"
include "simpl.mm"
include "modaddmod.mm"
include "cc.mm"
include "recn.mm"
include "recnd.mm"
include "addassd.mm"
include "1cnd.mm"
include "adddird.mm"
include "mulid2d.mm"
include "com13.mm"
include "adantld.mm"
include "3eqtrd.mm"
include "biimpd.mm"
include "a2d.mm"
include "nn0ind.mm"
include "ralrimiv.mm"

theorem cshweqrep
  let vj: setvar j
  let cI: class I
  let cL: class L
  let cV: class V
  let cW: class W
  let vy: setvar y
  let vx: setvar x

  disjoint I j
  disjoint L j
  disjoint V j
  disjoint W j
  disjoint I y
  disjoint I x
  disjoint j y
  disjoint j x
  disjoint x y
  disjoint L x
  disjoint L y
  disjoint V x
  disjoint V y
  disjoint W x
  disjoint W y
  assert |- ( ( W e. Word V /\ L e. ZZ ) -> ( ( ( W cyclShift L ) = W /\ I e. ( 0 ..^ ( # ` W ) ) ) -> A. j e. NN0 ( W ` I ) = ( W ` ( ( I + ( j x. L ) ) mod ( # ` W ) ) ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cL
    cz
    wcel
    #
    wa
    #
    cW
    cL
    ccsh
    co
    #
    cW
    wceq
    #
    cI
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    #
    wa
    #
    cI
    cW
    cfv
    #
    cI
    vj
    cv
    #
    cL
    cmul
    co
    #
    caddc
    co
    #
    @5
    cmo
    co
    #
    cW
    cfv
    #
    wceq
    #
    vj
    cn0
    wral
    @2
    @8
    wa
    #
    @15
    vj
    cn0
    @10
    cn0
    wcel
    @16
    @15
    @16
    @9
    cI
    vx
    cv
    #
    cL
    cmul
    co
    #
    caddc
    co
    #
    @5
    cmo
    co
    #
    cW
    cfv
    #
    wceq
    #
    wi
    @16
    @9
    cI
    cc0
    cL
    cmul
    co
    #
    caddc
    co
    #
    @5
    cmo
    co
    #
    cW
    cfv
    #
    wceq
    #
    wi
    @16
    @9
    cI
    vy
    cv
    #
    cL
    cmul
    co
    #
    caddc
    co
    #
    @5
    cmo
    co
    #
    cW
    cfv
    #
    wceq
    #
    wi
    @16
    @9
    cI
    @28
    c1
    caddc
    co
    #
    cL
    cmul
    co
    #
    caddc
    co
    #
    @5
    cmo
    co
    #
    cW
    cfv
    #
    wceq
    #
    wi
    @16
    @15
    wi
    vx
    vy
    @10
    @17
    cc0
    wceq
    #
    @22
    @27
    @16
    @40
    @21
    @26
    @9
    @40
    @20
    @25
    cW
    @40
    @19
    @24
    @5
    cmo
    @40
    @18
    @23
    cI
    caddc
    @17
    cc0
    cL
    cmul
    oveq1
    oveq2d
    oveq1d
    fveq2d
    eqeq2d
    imbi2d
    vx
    vy
    weq
    #
    @22
    @33
    @16
    @41
    @21
    @32
    @9
    @41
    @20
    @31
    cW
    @41
    @19
    @30
    @5
    cmo
    @41
    @18
    @29
    cI
    caddc
    @17
    @28
    cL
    cmul
    oveq1
    oveq2d
    oveq1d
    fveq2d
    eqeq2d
    imbi2d
    @17
    @34
    wceq
    #
    @22
    @39
    @16
    @42
    @21
    @38
    @9
    @42
    @20
    @37
    cW
    @42
    @19
    @36
    @5
    cmo
    @42
    @18
    @35
    cI
    caddc
    @17
    @34
    cL
    cmul
    oveq1
    oveq2d
    oveq1d
    fveq2d
    eqeq2d
    imbi2d
    vx
    vj
    weq
    #
    @22
    @15
    @16
    @43
    @21
    @14
    @9
    @43
    @20
    @13
    cW
    @43
    @19
    @12
    @5
    cmo
    @43
    @18
    @11
    cI
    caddc
    @17
    @10
    cL
    cmul
    oveq1
    oveq2d
    oveq1d
    fveq2d
    eqeq2d
    imbi2d
    @16
    cI
    @25
    cW
    @16
    @25
    cI
    @5
    cmo
    co
    #
    cI
    @16
    @24
    cI
    @5
    cmo
    @16
    @24
    cI
    cc0
    caddc
    co
    #
    cI
    @16
    @23
    cc0
    cI
    caddc
    @2
    @23
    cc0
    wceq
    #
    @8
    @1
    @46
    @0
    @1
    cL
    cL
    zcn
    mul02d
    adantl
    adantr
    oveq2d
    @7
    @45
    cI
    wceq
    @2
    @4
    @7
    cI
    @7
    cI
    cI
    cc0
    @5
    elfzoelz
    zcnd
    addid1d
    ad2antll
    eqtrd
    oveq1d
    @7
    @44
    cI
    wceq
    @2
    @4
    cI
    @5
    zmodidfzoimp
    ad2antll
    eqtr2d
    fveq2d
    @28
    cn0
    wcel
    #
    @16
    @33
    @39
    @47
    @16
    @33
    @39
    wi
    @47
    @16
    wa
    #
    @33
    @39
    @48
    @32
    @38
    @9
    @48
    @32
    @31
    @3
    cfv
    #
    @31
    cL
    caddc
    co
    @5
    cmo
    co
    #
    cW
    cfv
    #
    @38
    @16
    @32
    @49
    wceq
    #
    @47
    @4
    @52
    @2
    @7
    @52
    cW
    @3
    @31
    cW
    @3
    fveq1
    eqcoms
    ad2antrl
    adantl
    @48
    @0
    @1
    @31
    @6
    wcel
    #
    @49
    @51
    wceq
    @47
    @0
    @1
    @8
    simprll
    @47
    @0
    @1
    @8
    simprlr
    @48
    @30
    cz
    wcel
    #
    @5
    cn
    wcel
    #
    wa
    #
    @53
    @16
    @47
    @56
    @2
    @8
    @47
    @56
    wi
    #
    @1
    @8
    @57
    wi
    @0
    @8
    @1
    @57
    @8
    @1
    @47
    @56
    @7
    @1
    @47
    wa
    #
    @56
    wi
    #
    @4
    @7
    cI
    cn0
    wcel
    #
    @55
    cI
    @5
    clt
    wbr
    #
    w3a
    #
    @59
    cI
    @5
    elfzo0
    #
    @60
    @55
    @59
    @61
    @60
    @55
    wa
    #
    @58
    @56
    @64
    @58
    wa
    @54
    @55
    @64
    cI
    cz
    wcel
    #
    @29
    cz
    wcel
    #
    @54
    @58
    @60
    @65
    @55
    cI
    nn0z
    adantr
    @47
    @1
    @66
    @47
    @28
    cz
    wcel
    @1
    @66
    @28
    nn0z
    @28
    cL
    zmulcl
    sylan
    ancoms
    cI
    @29
    zaddcl
    syl2an
    @60
    @55
    @58
    simplr
    jca
    ex
    3adant3
    sylbi
    adantl
    expd
    com12
    adantl
    imp
    impcom
    @30
    @5
    zmodfzo
    syl
    @31
    cL
    cV
    cW
    cshwidxmod
    syl3anc
    @48
    @50
    @37
    cW
    @16
    @47
    @50
    @37
    wceq
    #
    @8
    @2
    @47
    @67
    wi
    #
    @7
    @2
    @68
    wi
    @4
    @7
    @1
    @68
    @0
    @7
    @1
    @47
    @67
    @7
    @62
    @58
    @67
    wi
    #
    @63
    @60
    @55
    @69
    @61
    @60
    @55
    @69
    @60
    cI
    cr
    wcel
    #
    @55
    @69
    wi
    cI
    nn0re
    @58
    @55
    @70
    @67
    @1
    cL
    cr
    wcel
    #
    @28
    cr
    wcel
    #
    @55
    @70
    @67
    wi
    #
    wi
    @47
    cL
    zre
    @28
    nn0re
    @55
    @71
    @72
    wa
    #
    @73
    @55
    @74
    @70
    @67
    @55
    @5
    crp
    wcel
    #
    @74
    @70
    wa
    #
    @67
    wi
    @5
    nnrp
    @75
    @76
    @67
    @75
    @76
    wa
    #
    @50
    @30
    cL
    caddc
    co
    #
    @5
    cmo
    co
    #
    @37
    @77
    @30
    cr
    wcel
    #
    @71
    @75
    @50
    @79
    wceq
    @76
    @80
    @75
    @70
    @74
    @80
    @74
    @70
    @29
    cr
    wcel
    #
    @80
    @72
    @71
    @81
    @28
    cL
    remulcl
    #
    ancoms
    cI
    @29
    readdcl
    sylan2
    ancoms
    adantl
    @75
    @71
    @72
    @70
    simprll
    @75
    @76
    simpl
    @30
    cL
    @5
    modaddmod
    syl3anc
    @77
    @78
    @36
    @5
    cmo
    @76
    @78
    @36
    wceq
    @75
    @76
    @78
    cI
    @29
    cL
    caddc
    co
    #
    caddc
    co
    @36
    @76
    cI
    @29
    cL
    @70
    cI
    cc
    wcel
    @74
    cI
    recn
    adantl
    @74
    @29
    cc
    wcel
    #
    @70
    @72
    @71
    @84
    @72
    @71
    wa
    @29
    @82
    recnd
    ancoms
    adantr
    @74
    cL
    cc
    wcel
    #
    @70
    @71
    @85
    @72
    cL
    recn
    #
    adantr
    #
    adantr
    addassd
    @76
    @83
    @35
    cI
    caddc
    @74
    @83
    @35
    wceq
    @70
    @74
    @35
    @29
    c1
    cL
    cmul
    co
    #
    caddc
    co
    @83
    @74
    @28
    c1
    cL
    @72
    @28
    cc
    wcel
    @71
    @28
    recn
    adantl
    @74
    1cnd
    @87
    adddird
    @74
    @88
    cL
    @29
    caddc
    @71
    @88
    cL
    wceq
    @72
    @71
    cL
    @86
    mulid2d
    adantr
    oveq2d
    eqtr2d
    adantr
    oveq2d
    eqtrd
    adantl
    oveq1d
    eqtrd
    ex
    syl
    expd
    com12
    syl2an
    com13
    syl
    imp
    3adant3
    sylbi
    expd
    adantld
    adantl
    impcom
    impcom
    fveq2d
    3eqtrd
    eqeq2d
    biimpd
    ex
    a2d
    nn0ind
    com12
    ralrimiv
    ex
end
