include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cfz.mm"
include "cv.mm"
include "cmul.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cdvr.mm"
include "cneg.mm"
include "cexp.mm"
include "cmulr.mm"
include "cur.mm"
include "cof.mm"
include "ccom.mm"
include "cmo.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "oveq2i.mm"
include "cbs.mm"
include "cfn.mm"
include "c0g.mm"
include "eqid.mm"
include "mgpbas.mm"
include "ccrg.mm"
include "wcel.mm"
include "ccmn.mm"
include "cfield.mm"
include "cprime.mm"
include "csn.mm"
include "eldifad.mm"
include "znfld.mm"
include "syl.mm"
include "cdr.mm"
include "isfld.mm"
include "simprbi.mm"
include "crngmgp.mm"
include "fzfid.mm"
include "cz.mm"
include "wf.mm"
include "zring.mm"
include "crh.mm"
include "crg.mm"
include "crngring.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "rhmf.mm"
include "2z.mm"
include "elfzelz.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "fmptd.mm"
include "cvv.mm"
include "wa.mm"
include "fvexd.mm"
include "fsuppmptdm.mm"
include "lgseisenlem2.mm"
include "gsumf1o.mm"
include "syl5eqr.mm"
include "wral.mm"
include "lgseisenlem1.mm"
include "fmpt.mm"
include "sylibr.mm"
include "a1i.mm"
include "eqidd.mm"
include "fmptcof.mm"
include "oveq2d.mm"
include "cn0.mm"
include "adantr.mm"
include "prmz.mm"
include "cn.mm"
include "2nn.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnmulcl.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "prmnn.mm"
include "zmodcld.mm"
include "syl5eqel.mm"
include "nn0zd.mm"
include "m1expcl.mm"
include "nn0cnd.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan2d.mm"
include "cdvds.mm"
include "wbr.mm"
include "nnrpd.mm"
include "oveq1i.mm"
include "cr.mm"
include "crp.mm"
include "zred.mm"
include "modabs2.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "modmul12d.mm"
include "zcnd.mm"
include "mulassd.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "wb.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "nnnn0d.mm"
include "zndvds.mm"
include "mpbird.mm"
include "zringmulr.mm"
include "rhmmul.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "ffvelrnd.mm"
include "offval2.mm"
include "eqtr4d.mm"
include "mgpplusg.mm"
include "gsummptfidmadd2.mm"
include "eqtrd.mm"
include "cui.mm"
include "csubmnd.mm"
include "unitsubm.mm"
include "wn.mm"
include "cle.mm"
include "elfzle2.mm"
include "clt.mm"
include "nnred.mm"
include "cuz.mm"
include "prmuz2.mm"
include "uz2m1nn.mm"
include "3syl.mm"
include "2re.mm"
include "2pos.mm"
include "lemuldiv2.mm"
include "syl112anc.mm"
include "peano2zm.mm"
include "fznn.mm"
include "mpbir2and.mm"
include "fzm1ndvds.mm"
include "zndvds0.mm"
include "necon3abid.mm"
include "simplbi.mm"
include "drngunit.mm"
include "gsumsubmcl.mm"
include "dvrid.mm"
include "gsumcl.mm"
include "dvrcan3.mm"
include "3eqtr3rd.mm"

theorem lgseisenlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cG: class G
  let cL: class L
  let cM: class M
  let cY: class Y
  let vk: setvar k
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cN: class N
  assume lgseisen.1: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume lgseisen.2: |- ( ph -> Q e. ( Prime \ { 2 } ) )
  assume lgseisen.3: |- ( ph -> P =/= Q )
  assume lgseisen.4: |- R = ( ( Q x. ( 2 x. x ) ) mod P )
  assume lgseisen.5: |- M = ( x e. ( 1 ... ( ( P - 1 ) / 2 ) ) |-> ( ( ( ( -u 1 ^ R ) x. R ) mod P ) / 2 ) )
  assume lgseisen.6: |- S = ( ( Q x. ( 2 x. y ) ) mod P )
  assume lgseisen.7: |- Y = ( Z/nZ ` P )
  assume lgseisen.8: |- G = ( mulGrp ` Y )
  assume lgseisen.9: |- L = ( ZRHom ` Y )

  disjoint G x
  disjoint L x
  disjoint x y
  disjoint P x
  disjoint P y
  disjoint ph x
  disjoint ph y
  disjoint M y
  disjoint Q x
  disjoint Q y
  disjoint Y x
  disjoint S x
  disjoint k x
  disjoint G k
  disjoint L k
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint P k
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint P n
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint P u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint P v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint P w
  disjoint x z
  disjoint y z
  disjoint P z
  disjoint k ph
  disjoint n ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint M n
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint M z
  disjoint N u
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Q k
  disjoint Q u
  disjoint Q w
  disjoint Q z
  disjoint Y k
  disjoint R k
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S z
  assert |- ( ph -> ( G gsum ( x e. ( 1 ... ( ( P - 1 ) / 2 ) ) |-> ( L ` ( ( -u 1 ^ R ) x. Q ) ) ) ) = ( 1r ` Y ) )

  proof
    wph
    cG
    vx
    c1
    cP
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cfz
    co
    #
    c2
    vx
    cv
    #
    cmul
    co
    #
    cL
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    @7
    cY
    cdvr
    cfv
    #
    co
    #
    cG
    vx
    @2
    c1
    cneg
    cR
    cexp
    co
    #
    cQ
    cmul
    co
    #
    cL
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    @7
    cY
    cmulr
    cfv
    #
    co
    #
    @7
    @8
    co
    #
    cY
    cur
    cfv
    #
    @14
    wph
    @7
    @16
    @7
    @8
    wph
    @7
    cG
    @13
    @6
    @15
    cof
    co
    #
    cgsu
    co
    #
    @16
    wph
    @7
    cG
    vk
    @2
    c2
    vk
    cv
    #
    cmul
    co
    #
    cL
    cfv
    #
    cmpt
    #
    cM
    ccom
    #
    cgsu
    co
    #
    cG
    vx
    @2
    c2
    @10
    cR
    cmul
    co
    #
    cP
    cmo
    co
    #
    c2
    cdiv
    co
    #
    cmul
    co
    #
    cL
    cfv
    #
    cmpt
    #
    cgsu
    co
    @20
    wph
    @7
    cG
    @24
    cgsu
    co
    @26
    @24
    @6
    cG
    cgsu
    vk
    vx
    @2
    @23
    @5
    @21
    @3
    wceq
    @22
    @4
    cL
    @21
    @3
    c2
    cmul
    oveq2
    fveq2d
    cbvmptv
    oveq2i
    wph
    @2
    cY
    cbs
    cfv
    #
    @2
    @24
    cG
    cM
    cfn
    cG
    c0g
    cfv
    #
    @33
    cY
    cG
    lgseisen.8
    @33
    eqid
    #
    mgpbas
    #
    @34
    eqid
    #
    wph
    cY
    ccrg
    wcel
    #
    cG
    ccmn
    wcel
    wph
    cY
    cfield
    wcel
    #
    @38
    wph
    cP
    cprime
    wcel
    #
    @39
    wph
    cP
    cprime
    c2
    csn
    #
    lgseisen.1
    eldifad
    #
    cP
    cY
    lgseisen.7
    znfld
    syl
    #
    @39
    cY
    cdr
    wcel
    #
    @38
    cY
    isfld
    #
    simprbi
    syl
    #
    cY
    cG
    lgseisen.8
    crngmgp
    syl
    #
    wph
    c1
    @1
    fzfid
    #
    wph
    vk
    @2
    @23
    @33
    @24
    wph
    cz
    @33
    cL
    wf
    #
    @22
    cz
    wcel
    #
    @23
    @33
    wcel
    @21
    @2
    wcel
    #
    wph
    cL
    zring
    cY
    crh
    co
    wcel
    #
    @49
    wph
    cY
    crg
    wcel
    #
    @52
    wph
    @38
    @53
    @46
    cY
    crngring
    syl
    #
    cY
    cL
    lgseisen.9
    zrhrhm
    syl
    #
    cz
    @33
    zring
    cY
    cL
    zringbas
    @35
    rhmf
    syl
    #
    @51
    c2
    cz
    wcel
    @21
    cz
    wcel
    @50
    2z
    @21
    c1
    @1
    elfzelz
    c2
    @21
    zmulcl
    sylancr
    cz
    @33
    @22
    cL
    ffvelrn
    syl2an
    @24
    eqid
    #
    fmptd
    wph
    vk
    @2
    @24
    cvv
    cvv
    @23
    @34
    @57
    @48
    wph
    @51
    wa
    @22
    cL
    fvexd
    wph
    cG
    c0g
    fvexd
    #
    fsuppmptdm
    wph
    vx
    vy
    cP
    cQ
    cR
    cS
    cM
    lgseisen.1
    lgseisen.2
    lgseisen.3
    lgseisen.4
    lgseisen.5
    lgseisen.6
    lgseisenlem2
    gsumf1o
    syl5eqr
    wph
    @25
    @32
    cG
    cgsu
    wph
    vx
    vk
    @2
    @2
    @29
    @23
    @31
    cM
    @24
    wph
    @2
    @2
    cM
    wf
    @29
    @2
    wcel
    vx
    @2
    wral
    wph
    vx
    cP
    cQ
    cR
    cM
    lgseisen.1
    lgseisen.2
    lgseisen.3
    lgseisen.4
    lgseisen.5
    lgseisenlem1
    vx
    @2
    @2
    @29
    cM
    lgseisen.5
    fmpt
    sylibr
    cM
    vx
    @2
    @29
    cmpt
    wceq
    wph
    lgseisen.5
    a1i
    wph
    @24
    eqidd
    @21
    @29
    wceq
    @22
    @30
    cL
    @21
    @29
    c2
    cmul
    oveq2
    fveq2d
    fmptcof
    oveq2d
    wph
    @32
    @19
    cG
    cgsu
    wph
    @32
    vx
    @2
    @12
    @5
    @15
    co
    #
    cmpt
    @19
    wph
    vx
    @2
    @31
    @59
    wph
    @3
    @2
    wcel
    #
    wa
    #
    @31
    @28
    cL
    cfv
    #
    @11
    @4
    cmul
    co
    #
    cL
    cfv
    #
    @59
    @61
    @30
    @28
    cL
    @61
    @28
    c2
    @61
    @28
    @61
    @27
    cP
    @61
    @10
    cR
    @61
    cR
    cz
    wcel
    @10
    cz
    wcel
    @61
    cR
    @61
    cR
    cQ
    @4
    cmul
    co
    #
    cP
    cmo
    co
    #
    cn0
    lgseisen.4
    @61
    @65
    cP
    @61
    cQ
    @4
    @61
    cQ
    cprime
    wcel
    #
    cQ
    cz
    wcel
    wph
    @67
    @60
    wph
    cQ
    cprime
    @41
    lgseisen.2
    eldifad
    adantr
    cQ
    prmz
    syl
    #
    @61
    @4
    @61
    c2
    cn
    wcel
    @3
    cn
    wcel
    #
    @4
    cn
    wcel
    #
    2nn
    @60
    @69
    wph
    @3
    @1
    elfznn
    adantl
    #
    c2
    @3
    nnmulcl
    sylancr
    #
    nnzd
    #
    zmulcld
    #
    @61
    @40
    cP
    cn
    wcel
    #
    wph
    @40
    @60
    @42
    adantr
    #
    cP
    prmnn
    #
    syl
    #
    zmodcld
    syl5eqel
    nn0zd
    #
    cR
    m1expcl
    syl
    #
    @79
    zmulcld
    #
    @78
    zmodcld
    #
    nn0cnd
    @61
    2cnd
    c2
    cc0
    wne
    @61
    2ne0
    a1i
    divcan2d
    fveq2d
    @61
    @62
    @64
    wceq
    #
    cP
    @28
    @63
    cmin
    co
    cdvds
    wbr
    #
    @61
    @28
    cP
    cmo
    co
    #
    @63
    cP
    cmo
    co
    #
    wceq
    #
    @84
    @61
    @28
    @10
    @65
    cmul
    co
    #
    cP
    cmo
    co
    @85
    @86
    @61
    @10
    @10
    cR
    @65
    cP
    @80
    @80
    @79
    @74
    @61
    cP
    @78
    nnrpd
    #
    @61
    @10
    cP
    cmo
    co
    eqidd
    @61
    cR
    cP
    cmo
    co
    @66
    cP
    cmo
    co
    #
    @66
    cR
    @66
    cP
    cmo
    lgseisen.4
    oveq1i
    @61
    @65
    cr
    wcel
    cP
    crp
    wcel
    #
    @90
    @66
    wceq
    @61
    @65
    @74
    zred
    @89
    @65
    cP
    modabs2
    syl2anc
    syl5eq
    modmul12d
    @61
    @27
    cr
    wcel
    @91
    @85
    @28
    wceq
    @61
    @27
    @81
    zred
    @89
    @27
    cP
    modabs2
    syl2anc
    @61
    @63
    @88
    cP
    cmo
    @61
    @10
    cQ
    @4
    @61
    @10
    @80
    zcnd
    @61
    cQ
    @68
    zcnd
    @61
    @4
    @73
    zcnd
    mulassd
    oveq1d
    3eqtr4d
    @61
    @75
    @28
    cz
    wcel
    #
    @63
    cz
    wcel
    #
    @87
    @84
    wb
    wph
    @75
    @60
    wph
    @40
    @75
    @42
    @77
    syl
    adantr
    @61
    @28
    @82
    nn0zd
    #
    @61
    @11
    @4
    @61
    @10
    cQ
    @80
    @68
    zmulcld
    #
    @73
    zmulcld
    #
    @28
    @63
    cP
    moddvds
    syl3anc
    mpbid
    @61
    cP
    cn0
    wcel
    #
    @92
    @93
    @83
    @84
    wb
    @61
    cP
    @78
    nnnn0d
    #
    @94
    @96
    @28
    @63
    cL
    cP
    cY
    lgseisen.7
    lgseisen.9
    zndvds
    syl3anc
    mpbird
    @61
    @52
    @11
    cz
    wcel
    @4
    cz
    wcel
    #
    @64
    @59
    wceq
    wph
    @52
    @60
    @55
    adantr
    @95
    @73
    @11
    @4
    zring
    cY
    cmul
    @15
    cL
    cz
    zringbas
    zringmulr
    @15
    eqid
    #
    rhmmul
    syl3anc
    3eqtrd
    mpteq2dva
    wph
    vx
    @2
    @12
    @5
    @15
    @13
    @6
    cfn
    @33
    @33
    @48
    @61
    cz
    @33
    @11
    cL
    wph
    @49
    @60
    @56
    adantr
    #
    @95
    ffvelrnd
    #
    @61
    cz
    @33
    @4
    cL
    @101
    @73
    ffvelrnd
    #
    wph
    @13
    eqidd
    wph
    @6
    eqidd
    offval2
    eqtr4d
    oveq2d
    3eqtrd
    wph
    vx
    @2
    @33
    @12
    @5
    @15
    @13
    cG
    @6
    @36
    cY
    @15
    cG
    lgseisen.8
    @100
    mgpplusg
    @47
    @48
    @102
    @103
    @13
    eqid
    #
    @6
    eqid
    #
    gsummptfidmadd2
    eqtrd
    oveq1d
    wph
    @53
    @7
    cY
    cui
    cfv
    #
    wcel
    #
    @9
    @18
    wceq
    @54
    wph
    @2
    @106
    @6
    cG
    cfn
    @34
    @37
    @47
    @48
    wph
    @53
    @106
    cG
    csubmnd
    cfv
    wcel
    @54
    cY
    @106
    cG
    @106
    eqid
    #
    lgseisen.8
    unitsubm
    syl
    wph
    vx
    @2
    @5
    @106
    @6
    @61
    @5
    @106
    wcel
    #
    @5
    @33
    wcel
    #
    @5
    cY
    c0g
    cfv
    #
    wne
    #
    @103
    @61
    @112
    cP
    @4
    cdvds
    wbr
    #
    wn
    #
    @61
    @75
    @4
    c1
    @0
    cfz
    co
    wcel
    #
    @114
    @78
    @61
    @115
    @70
    @4
    @0
    cle
    wbr
    #
    @72
    @61
    @116
    @3
    @1
    cle
    wbr
    #
    @60
    @117
    wph
    @3
    c1
    @1
    elfzle2
    adantl
    @61
    @3
    cr
    wcel
    @0
    cr
    wcel
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @116
    @117
    wb
    @61
    @3
    @71
    nnred
    @61
    @0
    @61
    @40
    cP
    c2
    cuz
    cfv
    wcel
    @0
    cn
    wcel
    @76
    cP
    prmuz2
    cP
    uz2m1nn
    3syl
    nnred
    @118
    @61
    2re
    a1i
    @119
    @61
    2pos
    a1i
    @3
    @0
    c2
    lemuldiv2
    syl112anc
    mpbird
    @61
    @0
    cz
    wcel
    #
    @115
    @70
    @116
    wa
    wb
    @61
    cP
    cz
    wcel
    #
    @120
    @61
    @40
    @121
    @76
    cP
    prmz
    syl
    cP
    peano2zm
    syl
    @4
    @0
    fznn
    syl
    mpbir2and
    cP
    @4
    fzm1ndvds
    syl2anc
    @61
    @113
    @5
    @111
    @61
    @97
    @99
    @5
    @111
    wceq
    @113
    wb
    @98
    @73
    @4
    cL
    cP
    cY
    @111
    lgseisen.7
    lgseisen.9
    @111
    eqid
    #
    zndvds0
    syl2anc
    necon3abid
    mpbird
    @61
    @44
    @109
    @110
    @112
    wa
    wb
    wph
    @44
    @60
    wph
    @39
    @44
    @43
    @39
    @44
    @38
    @45
    simplbi
    syl
    adantr
    @33
    cY
    @106
    @5
    @111
    @35
    @108
    @122
    drngunit
    syl
    mpbir2and
    @105
    fmptd
    wph
    vx
    @2
    @6
    cvv
    cvv
    @5
    @34
    @105
    @48
    @61
    @4
    cL
    fvexd
    @58
    fsuppmptdm
    gsumsubmcl
    #
    @8
    cY
    @106
    @18
    @7
    @108
    @8
    eqid
    #
    @18
    eqid
    dvrid
    syl2anc
    wph
    @53
    @14
    @33
    wcel
    @107
    @17
    @14
    wceq
    @54
    wph
    @2
    @33
    @13
    cG
    cfn
    @34
    @36
    @37
    @47
    @48
    wph
    vx
    @2
    @12
    @33
    @13
    @102
    @104
    fmptd
    wph
    vx
    @2
    @13
    cvv
    cvv
    @12
    @34
    @104
    @48
    @61
    @11
    cL
    fvexd
    @58
    fsuppmptdm
    gsumcl
    @123
    @33
    @8
    cY
    @15
    @106
    @14
    @7
    @35
    @108
    @124
    @100
    dvrcan3
    syl3anc
    3eqtr3rd
end
