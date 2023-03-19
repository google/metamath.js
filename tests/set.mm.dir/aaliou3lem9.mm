include "caa.mm"
include "wcel.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cexp.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cn.mm"
include "wral.mm"
include "cz.mm"
include "crp.mm"
include "wrex.mm"
include "wa.mm"
include "wn.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "cfa.mm"
include "cneg.mm"
include "cmul.mm"
include "cle.mm"
include "aaliou3lem8.mm"
include "aaliou3lem6.mm"
include "ad2antrl.mm"
include "cn0.mm"
include "2nn.mm"
include "nnnn0.mm"
include "faccl.mm"
include "3syl.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "cr.mm"
include "aaliou3lem5.mm"
include "recnd.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan4d.mm"
include "wne.mm"
include "aaliou3lem7.mm"
include "simpld.mm"
include "eqnetrd.mm"
include "necomd.mm"
include "neneqd.mm"
include "aaliou3lem4.mm"
include "nnred.mm"
include "remulcld.mm"
include "nndivred.mm"
include "resubcl.mm"
include "abscld.mm"
include "2rp.mm"
include "peano2nn0.mm"
include "nnz.mm"
include "znegcl.mm"
include "rpexpcl.mm"
include "rpmulcl.mm"
include "rpred.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "nnexpcld.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "simprd.mm"
include "eqbrtrd.mm"
include "simprr.mm"
include "letrd.mm"
include "lenltd.mm"
include "mpbid.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "notbid.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "breq12d.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "rexlimddv.mm"
include "pm4.56.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "sylib.mm"
include "nrexdv.mm"
include "nrex.mm"
include "aaliou2b.mm"
include "mto.mm"

theorem aaliou3lem9
  let cF: class F
  let cH: class H
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let cA: class A
  assume aaliou3lem.c: |- F = ( a e. NN |-> ( 2 ^ -u ( ! ` a ) ) )
  assume aaliou3lem.d: |- L = sum_ b e. NN ( F ` b )
  assume aaliou3lem.e: |- H = ( c e. NN |-> sum_ b e. ( 1 ... c ) ( F ` b ) )

  disjoint a b
  disjoint a c
  disjoint b c
  disjoint F b
  disjoint F c
  disjoint L c
  disjoint L a
  disjoint L b
  disjoint a d
  disjoint a e
  disjoint b d
  disjoint b e
  disjoint c d
  disjoint c e
  disjoint d e
  disjoint F d
  disjoint F e
  disjoint L d
  disjoint L e
  disjoint L f
  disjoint c f
  disjoint d f
  disjoint e f
  disjoint H d
  disjoint H e
  disjoint H f
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint a f
  disjoint b f
  assert |- -. L e. AA

  proof
    cL
    caa
    wcel
    cL
    vf
    cv
    #
    vd
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vb
    cv
    #
    @1
    va
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cL
    @2
    cmin
    co
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    wo
    #
    vd
    cn
    wral
    #
    vf
    cz
    wral
    #
    vb
    crp
    wrex
    #
    va
    cn
    wrex
    @14
    va
    cn
    @5
    cn
    wcel
    #
    @13
    vb
    crp
    @15
    @4
    crp
    wcel
    #
    wa
    #
    @3
    wn
    #
    @10
    wn
    #
    wa
    #
    vd
    cn
    wrex
    #
    vf
    cz
    wrex
    #
    @13
    wn
    #
    @17
    c2
    c2
    ve
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
    @4
    c2
    @24
    cfa
    cfv
    #
    cexp
    co
    #
    @5
    cexp
    co
    #
    cdiv
    co
    #
    cle
    wbr
    #
    @22
    ve
    cn
    ve
    @5
    @4
    aaliou3lem8
    @17
    @24
    cn
    wcel
    #
    @34
    wa
    #
    wa
    #
    @24
    cH
    cfv
    #
    @31
    cmul
    co
    #
    cz
    wcel
    #
    @31
    cn
    wcel
    #
    cL
    @39
    @31
    cdiv
    co
    #
    wceq
    #
    wn
    #
    @33
    cL
    @42
    cmin
    co
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    wn
    #
    @22
    @35
    @40
    @17
    @34
    @24
    cF
    cH
    cL
    va
    vb
    vc
    aaliou3lem.c
    aaliou3lem.d
    aaliou3lem.e
    aaliou3lem6
    ad2antrl
    @37
    c2
    cn
    wcel
    @30
    cn0
    wcel
    #
    @41
    2nn
    @37
    @24
    cn0
    wcel
    #
    @30
    cn
    wcel
    @49
    @35
    @50
    @17
    @34
    @24
    nnnn0
    ad2antrl
    #
    @24
    faccl
    @30
    nnnn0
    3syl
    c2
    @30
    nnexpcl
    sylancr
    #
    @37
    cL
    @42
    @37
    @42
    cL
    @37
    @42
    @38
    cL
    @37
    @38
    @31
    @37
    @38
    @35
    @38
    cr
    wcel
    @17
    @34
    @24
    cF
    cH
    cL
    va
    vb
    vc
    aaliou3lem.c
    aaliou3lem.d
    aaliou3lem.e
    aaliou3lem5
    ad2antrl
    #
    recnd
    @37
    @31
    @52
    nncnd
    @37
    @31
    @52
    nnne0d
    divcan4d
    #
    @35
    @38
    cL
    wne
    #
    @17
    @34
    @35
    @55
    cL
    @38
    cmin
    co
    #
    cabs
    cfv
    #
    @29
    cle
    wbr
    #
    @24
    cF
    cH
    cL
    va
    vb
    vc
    aaliou3lem.c
    aaliou3lem.d
    aaliou3lem.e
    aaliou3lem7
    #
    simpld
    ad2antrl
    eqnetrd
    necomd
    neneqd
    @37
    @46
    @33
    cle
    wbr
    @48
    @37
    @46
    @29
    @33
    @37
    @45
    @37
    @45
    @37
    cL
    cr
    wcel
    @42
    cr
    wcel
    @45
    cr
    wcel
    cF
    cH
    cL
    va
    vb
    vc
    aaliou3lem.c
    aaliou3lem.d
    aaliou3lem.e
    aaliou3lem4
    @37
    @39
    @31
    @37
    @38
    @31
    @53
    @37
    @31
    @52
    nnred
    remulcld
    @52
    nndivred
    cL
    @42
    resubcl
    sylancr
    recnd
    abscld
    #
    @37
    @29
    @37
    c2
    crp
    wcel
    #
    @28
    crp
    wcel
    #
    @29
    crp
    wcel
    2rp
    @37
    @61
    @27
    cz
    wcel
    #
    @62
    2rp
    @37
    @26
    cn
    wcel
    #
    @26
    cz
    wcel
    @63
    @37
    @50
    @25
    cn0
    wcel
    @64
    @51
    @24
    peano2nn0
    @25
    faccl
    3syl
    @26
    nnz
    @26
    znegcl
    3syl
    c2
    @27
    rpexpcl
    sylancr
    c2
    @28
    rpmulcl
    sylancr
    rpred
    @37
    @33
    @37
    @4
    @32
    @15
    @16
    @36
    simplr
    @37
    @32
    @37
    @31
    @5
    @52
    @15
    @5
    cn0
    wcel
    @16
    @36
    @5
    nnnn0
    ad2antrr
    nnexpcld
    nnrpd
    rpdivcld
    rpred
    #
    @37
    @46
    @57
    @29
    cle
    @37
    @45
    @56
    cabs
    @37
    @42
    @38
    cL
    cmin
    @54
    oveq2d
    fveq2d
    @35
    @58
    @17
    @34
    @35
    @55
    @58
    @59
    simprd
    ad2antrl
    eqbrtrd
    @17
    @35
    @34
    simprr
    letrd
    @37
    @46
    @33
    @60
    @65
    lenltd
    mpbid
    @20
    @44
    @48
    wa
    cL
    @39
    @1
    cdiv
    co
    #
    wceq
    #
    wn
    #
    @7
    cL
    @66
    cmin
    co
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    wn
    #
    wa
    vf
    vd
    @39
    @31
    cz
    cn
    @0
    @39
    wceq
    #
    @18
    @68
    @19
    @72
    @73
    @3
    @67
    @73
    @2
    @66
    cL
    @0
    @39
    @1
    cdiv
    oveq1
    #
    eqeq2d
    notbid
    @73
    @10
    @71
    @73
    @9
    @70
    @7
    clt
    @73
    @8
    @69
    cabs
    @73
    @2
    @66
    cL
    cmin
    @74
    oveq2d
    fveq2d
    breq2d
    notbid
    anbi12d
    @1
    @31
    wceq
    #
    @68
    @44
    @72
    @48
    @75
    @67
    @43
    @75
    @66
    @42
    cL
    @1
    @31
    @39
    cdiv
    oveq2
    #
    eqeq2d
    notbid
    @75
    @71
    @47
    @75
    @7
    @33
    @70
    @46
    clt
    @75
    @6
    @32
    @4
    cdiv
    @1
    @31
    @5
    cexp
    oveq1
    oveq2d
    @75
    @69
    @45
    cabs
    @75
    @66
    @42
    cL
    cmin
    @76
    oveq2d
    fveq2d
    breq12d
    notbid
    anbi12d
    rspc2ev
    syl112anc
    rexlimddv
    @22
    @12
    wn
    #
    vf
    cz
    wrex
    @23
    @21
    @77
    vf
    cz
    @21
    @11
    wn
    #
    vd
    cn
    wrex
    @77
    @20
    @78
    vd
    cn
    @3
    @10
    pm4.56
    rexbii
    @11
    vd
    cn
    rexnal
    bitri
    rexbii
    @12
    vf
    cz
    rexnal
    bitri
    sylib
    nrexdv
    nrex
    vb
    cL
    va
    vd
    vf
    aaliou2b
    mto
end
