include "cv.mm"
include "crn.mm"
include "cin.mm"
include "wcel.mm"
include "wex.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "cgz.mm"
include "wrex.mm"
include "cmin.mm"
include "cfz.mm"
include "c0.mm"
include "wne.mm"
include "4sqlem11.mm"
include "n0.mm"
include "sylib.mm"
include "cmo.mm"
include "wa.mm"
include "cc0.mm"
include "vex.mm"
include "weq.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab2.mm"
include "cab.mm"
include "abid.mm"
include "rexeqi.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "syl5bb.mm"
include "rexab.mm"
include "3bitri.mm"
include "rnmpt.mm"
include "eleq2i.mm"
include "rexcom4.mm"
include "r19.41v.mm"
include "exbii.mm"
include "bitri.mm"
include "3bitr4i.mm"
include "ovex.mm"
include "oveq2.mm"
include "ceqsexv.mm"
include "rexbii.mm"
include "anbi12i.mm"
include "elin.mm"
include "reeanv.mm"
include "eqtr2.mm"
include "w3a.mm"
include "cdiv.mm"
include "ci.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cdvds.mm"
include "cr.mm"
include "crp.mm"
include "cn.mm"
include "cn0.mm"
include "cprime.mm"
include "3ad2ant1.mm"
include "prmnn.mm"
include "syl.mm"
include "nnm1nn0.mm"
include "nn0red.mm"
include "nnrpd.mm"
include "nn0ge0d.mm"
include "nnred.mm"
include "ltm1d.mm"
include "modid.mm"
include "syl22anc.mm"
include "simp2r.mm"
include "elfzelz.mm"
include "zsqcl2.mm"
include "modlt.mm"
include "syl2anc.mm"
include "wb.mm"
include "zsqcl.mm"
include "zmodcld.mm"
include "nn0zd.mm"
include "prmz.mm"
include "zltlem1.mm"
include "mpbid.mm"
include "breqtrrd.mm"
include "modsubdir.mm"
include "syl3anc.mm"
include "simp3.mm"
include "3eqtr4rd.mm"
include "simp2l.mm"
include "zsubcld.mm"
include "moddvds.mm"
include "nn0cnd.mm"
include "subsub3d.mm"
include "nn0addcld.mm"
include "nncnd.mm"
include "1cnd.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "nn0p1nn.mm"
include "nnzd.mm"
include "dvdssubr.mm"
include "mpbird.mm"
include "nnne0d.mm"
include "dvdsval2.mm"
include "nnrp.mm"
include "rpdivcl.mm"
include "syl2an.mm"
include "rpgt0d.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "nnge1d.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "sylancr.mm"
include "resqcld.mm"
include "readdcld.mm"
include "1red.mm"
include "nnsqcld.mm"
include "zred.mm"
include "elfzle1.mm"
include "elfzle2.mm"
include "le2sq2.mm"
include "le2addd.mm"
include "2timesd.mm"
include "c4.mm"
include "2lt4.mm"
include "2re.mm"
include "a1i.mm"
include "4re.mm"
include "nngt0d.mm"
include "ltmul1.mm"
include "syl112anc.mm"
include "mpbii.mm"
include "cc.mm"
include "2cn.mm"
include "sqmul.mm"
include "sq2.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "lelttrd.mm"
include "ltaddrpd.mm"
include "lttrd.mm"
include "ltadd1dd.mm"
include "sqvald.mm"
include "binom21.mm"
include "3eqtr3d.mm"
include "ltdivmul.mm"
include "1z.mm"
include "elfzm11.mm"
include "mpbir3and.mm"
include "gzreim.mm"
include "cre.mm"
include "cim.mm"
include "gzcn.mm"
include "absvalsq2d.mm"
include "crred.mm"
include "crimd.mm"
include "oveq12d.mm"
include "divcan1d.mm"
include "eqtr4d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspc2ev.mm"
include "3expia.mm"
include "syl5.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem 4sqlem12
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cP: class P
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cB: class B
  let cE: class E
  let cG: class G
  let cH: class H
  let vj: setvar j
  let cC: class C
  let cD: class D
  let vi: setvar i
  let cM: class M
  let cT: class T
  let cR: class R
  assume 4sq.1: |- S = { n | E. x e. ZZ E. y e. ZZ E. z e. ZZ E. w e. ZZ n = ( ( ( x ^ 2 ) + ( y ^ 2 ) ) + ( ( z ^ 2 ) + ( w ^ 2 ) ) ) }
  assume 4sq.2: |- ( ph -> N e. NN )
  assume 4sq.3: |- ( ph -> P = ( ( 2 x. N ) + 1 ) )
  assume 4sq.4: |- ( ph -> P e. Prime )
  assume 4sqlem11.5: |- A = { u | E. m e. ( 0 ... N ) u = ( ( m ^ 2 ) mod P ) }
  assume 4sqlem11.6: |- F = ( v e. A |-> ( ( P - 1 ) - v ) )

  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint k n
  disjoint k v
  disjoint A k
  disjoint n v
  disjoint A n
  disjoint A v
  disjoint F n
  disjoint k u
  disjoint n u
  disjoint k m
  disjoint N k
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint N m
  disjoint N n
  disjoint u v
  disjoint N u
  disjoint N v
  disjoint P k
  disjoint P m
  disjoint P n
  disjoint P u
  disjoint P v
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph u
  disjoint ph v
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a n
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b d
  disjoint b n
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c d
  disjoint c n
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint d n
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B n
  disjoint E n
  disjoint G n
  disjoint H n
  disjoint a j
  disjoint a k
  disjoint a v
  disjoint A a
  disjoint b j
  disjoint b k
  disjoint b v
  disjoint A b
  disjoint c j
  disjoint c k
  disjoint c v
  disjoint A c
  disjoint d j
  disjoint d k
  disjoint d v
  disjoint A d
  disjoint j k
  disjoint j n
  disjoint j v
  disjoint A j
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C n
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D n
  disjoint F j
  disjoint a i
  disjoint a u
  disjoint M a
  disjoint b i
  disjoint b u
  disjoint M b
  disjoint c i
  disjoint c u
  disjoint M c
  disjoint d i
  disjoint d u
  disjoint M d
  disjoint i k
  disjoint i n
  disjoint i u
  disjoint M i
  disjoint M k
  disjoint M n
  disjoint M u
  disjoint a m
  disjoint P a
  disjoint b m
  disjoint P b
  disjoint c m
  disjoint P c
  disjoint d m
  disjoint P d
  disjoint i j
  disjoint i m
  disjoint i v
  disjoint P i
  disjoint j m
  disjoint j u
  disjoint P j
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint j ph
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S i
  disjoint S j
  disjoint T k
  disjoint T u
  disjoint R i
  assert |- ( ph -> E. k e. ( 1 ... ( P - 1 ) ) E. u e. Z[i] ( ( ( abs ` u ) ^ 2 ) + 1 ) = ( k x. P ) )

  proof
    wph
    vj
    cv
    #
    cA
    cF
    crn
    #
    cin
    #
    wcel
    #
    vj
    wex
    #
    vu
    cv
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    c1
    caddc
    co
    #
    vk
    cv
    #
    cP
    cmul
    co
    #
    wceq
    #
    vu
    cgz
    wrex
    vk
    c1
    cP
    c1
    cmin
    co
    #
    cfz
    co
    #
    wrex
    #
    wph
    @2
    c0
    wne
    @4
    wph
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cP
    cS
    vm
    vn
    cF
    cN
    4sq.1
    4sq.2
    4sq.3
    4sq.4
    4sqlem11.5
    4sqlem11.6
    4sqlem11
    vj
    @2
    n0
    sylib
    wph
    @3
    @14
    vj
    @3
    @0
    vm
    cv
    #
    c2
    cexp
    co
    #
    cP
    cmo
    co
    #
    wceq
    #
    @0
    @12
    vn
    cv
    #
    c2
    cexp
    co
    #
    cP
    cmo
    co
    #
    cmin
    co
    #
    wceq
    #
    wa
    #
    vn
    cc0
    cN
    cfz
    co
    #
    wrex
    vm
    @25
    wrex
    #
    wph
    @14
    @0
    cA
    wcel
    #
    @0
    @1
    wcel
    #
    wa
    @18
    vm
    @25
    wrex
    #
    @23
    vn
    @25
    wrex
    #
    wa
    @3
    @26
    @27
    @29
    @28
    @30
    @5
    @17
    wceq
    #
    vm
    @25
    wrex
    #
    @29
    vu
    @0
    cA
    vj
    vex
    vu
    vj
    weq
    @31
    @18
    vm
    @25
    @5
    @0
    @17
    eqeq1
    rexbidv
    4sqlem11.5
    elab2
    @28
    vv
    cv
    #
    @21
    wceq
    #
    @0
    @12
    @33
    cmin
    co
    #
    wceq
    #
    wa
    #
    vv
    wex
    #
    vn
    @25
    wrex
    #
    @30
    @0
    @36
    vv
    cA
    wrex
    #
    vj
    cab
    #
    wcel
    #
    @34
    vn
    @25
    wrex
    #
    @36
    wa
    #
    vv
    wex
    #
    @28
    @39
    @42
    @40
    @36
    vv
    @32
    vu
    cab
    #
    wrex
    @45
    @40
    vj
    abid
    @36
    vv
    cA
    @46
    4sqlem11.5
    rexeqi
    @32
    @43
    @36
    vv
    vu
    @32
    @5
    @21
    wceq
    #
    vn
    @25
    wrex
    vu
    vv
    weq
    #
    @43
    @31
    @47
    vm
    vn
    @25
    vm
    vn
    weq
    #
    @17
    @21
    @5
    @49
    @16
    @20
    cP
    cmo
    @15
    @19
    c2
    cexp
    oveq1
    oveq1d
    eqeq2d
    cbvrexv
    @48
    @47
    @34
    vn
    @25
    @5
    @33
    @21
    eqeq1
    rexbidv
    syl5bb
    rexab
    3bitri
    @1
    @41
    @0
    vv
    vj
    cA
    @35
    cF
    4sqlem11.6
    rnmpt
    eleq2i
    @39
    @37
    vn
    @25
    wrex
    #
    vv
    wex
    @45
    @37
    vn
    vv
    @25
    rexcom4
    @50
    @44
    vv
    @34
    @36
    vn
    @25
    r19.41v
    exbii
    bitri
    3bitr4i
    @38
    @23
    vn
    @25
    @36
    @23
    vv
    @21
    @20
    cP
    cmo
    ovex
    @34
    @35
    @22
    @0
    @33
    @21
    @12
    cmin
    oveq2
    eqeq2d
    ceqsexv
    rexbii
    bitri
    anbi12i
    @0
    cA
    @1
    elin
    @18
    @23
    vm
    vn
    @25
    @25
    reeanv
    3bitr4i
    wph
    @24
    @14
    vm
    vn
    @25
    @25
    @24
    @17
    @22
    wceq
    #
    wph
    @15
    @25
    wcel
    #
    @19
    @25
    wcel
    #
    wa
    #
    wa
    @14
    @0
    @17
    @22
    eqtr2
    wph
    @54
    @51
    @14
    wph
    @54
    @51
    w3a
    #
    @16
    @20
    caddc
    co
    #
    c1
    caddc
    co
    #
    cP
    cdiv
    co
    #
    @13
    wcel
    #
    @15
    ci
    @19
    cmul
    co
    caddc
    co
    #
    cgz
    wcel
    #
    @60
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    c1
    caddc
    co
    #
    @58
    cP
    cmul
    co
    #
    wceq
    #
    @14
    @55
    @59
    @58
    cz
    wcel
    #
    c1
    @58
    cle
    wbr
    #
    @58
    cP
    clt
    wbr
    #
    @55
    cP
    @57
    cdvds
    wbr
    #
    @67
    @55
    @70
    cP
    @57
    cP
    cmin
    co
    #
    cdvds
    wbr
    #
    @55
    cP
    @16
    @12
    @20
    cmin
    co
    #
    cmin
    co
    #
    @71
    cdvds
    @55
    @17
    @73
    cP
    cmo
    co
    #
    wceq
    #
    cP
    @74
    cdvds
    wbr
    #
    @55
    @12
    cP
    cmo
    co
    #
    @21
    cmin
    co
    #
    @22
    @75
    @17
    @55
    @78
    @12
    @21
    cmin
    @55
    @12
    cr
    wcel
    #
    cP
    crp
    wcel
    #
    cc0
    @12
    cle
    wbr
    @12
    cP
    clt
    wbr
    @78
    @12
    wceq
    @55
    @12
    @55
    cP
    cn
    wcel
    #
    @12
    cn0
    wcel
    @55
    cP
    cprime
    wcel
    #
    @82
    wph
    @54
    @83
    @51
    4sq.4
    3ad2ant1
    #
    cP
    prmnn
    syl
    #
    cP
    nnm1nn0
    syl
    #
    nn0red
    #
    @55
    cP
    @85
    nnrpd
    #
    @55
    @12
    @86
    nn0ge0d
    @55
    cP
    @55
    cP
    @85
    nnred
    #
    ltm1d
    @12
    cP
    modid
    syl22anc
    #
    oveq1d
    @55
    @21
    @78
    cle
    wbr
    #
    @75
    @79
    wceq
    #
    @55
    @21
    @12
    @78
    cle
    @55
    @21
    cP
    clt
    wbr
    #
    @21
    @12
    cle
    wbr
    #
    @55
    @20
    cr
    wcel
    #
    @81
    @93
    @55
    @20
    @55
    @19
    cz
    wcel
    #
    @20
    cn0
    wcel
    @55
    @53
    @96
    wph
    @52
    @53
    @51
    simp2r
    #
    @19
    cc0
    cN
    elfzelz
    syl
    #
    @19
    zsqcl2
    syl
    #
    nn0red
    #
    @88
    @20
    cP
    modlt
    syl2anc
    @55
    @21
    cz
    wcel
    cP
    cz
    wcel
    #
    @93
    @94
    wb
    @55
    @21
    @55
    @20
    cP
    @55
    @96
    @20
    cz
    wcel
    @98
    @19
    zsqcl
    syl
    #
    @85
    zmodcld
    nn0zd
    @55
    @83
    @101
    @84
    cP
    prmz
    syl
    #
    @21
    cP
    zltlem1
    syl2anc
    mpbid
    @90
    breqtrrd
    @55
    @80
    @95
    @81
    @91
    @92
    wb
    @87
    @100
    @88
    @12
    @20
    cP
    modsubdir
    syl3anc
    mpbid
    wph
    @54
    @51
    simp3
    3eqtr4rd
    @55
    @82
    @16
    cz
    wcel
    #
    @73
    cz
    wcel
    @76
    @77
    wb
    @85
    @55
    @15
    cz
    wcel
    #
    @104
    @55
    @52
    @105
    wph
    @52
    @53
    @51
    simp2l
    #
    @15
    cc0
    cN
    elfzelz
    syl
    #
    @15
    zsqcl
    syl
    @55
    @12
    @20
    @55
    @12
    @86
    nn0zd
    @102
    zsubcld
    @16
    @73
    cP
    moddvds
    syl3anc
    mpbid
    @55
    @74
    @56
    @12
    cmin
    co
    @71
    @55
    @16
    @12
    @20
    @55
    @16
    @55
    @105
    @16
    cn0
    wcel
    @107
    @15
    zsqcl2
    syl
    #
    nn0cnd
    @55
    @12
    @86
    nn0cnd
    @55
    @20
    @99
    nn0cnd
    subsub3d
    @55
    @56
    cP
    c1
    @55
    @56
    @55
    @16
    @20
    @108
    @99
    nn0addcld
    #
    nn0cnd
    @55
    cP
    @85
    nncnd
    #
    @55
    1cnd
    subsub3d
    eqtrd
    breqtrd
    @55
    @101
    @57
    cz
    wcel
    #
    @70
    @72
    wb
    @103
    @55
    @57
    @55
    @56
    cn0
    wcel
    @57
    cn
    wcel
    #
    @109
    @56
    nn0p1nn
    syl
    #
    nnzd
    #
    cP
    @57
    dvdssubr
    syl2anc
    mpbird
    @55
    @101
    cP
    cc0
    wne
    @111
    @70
    @67
    wb
    @103
    @55
    cP
    @85
    nnne0d
    #
    @114
    cP
    @57
    dvdsval2
    syl3anc
    mpbid
    #
    @55
    @58
    @55
    @67
    cc0
    @58
    clt
    wbr
    @58
    cn
    wcel
    @116
    @55
    @58
    @55
    @112
    @82
    @58
    crp
    wcel
    #
    @113
    @85
    @112
    @57
    crp
    wcel
    @81
    @117
    @82
    @57
    nnrp
    cP
    nnrp
    @57
    cP
    rpdivcl
    syl2an
    syl2anc
    rpgt0d
    @58
    elnnz
    sylanbrc
    nnge1d
    @55
    @69
    @57
    cP
    cP
    cmul
    co
    #
    clt
    wbr
    #
    @55
    @57
    c2
    cN
    cmul
    co
    #
    c2
    cexp
    co
    #
    c2
    @120
    cmul
    co
    #
    caddc
    co
    #
    c1
    caddc
    co
    #
    @118
    clt
    @55
    @56
    @123
    c1
    @55
    @56
    @109
    nn0red
    #
    @55
    @121
    @122
    @55
    @120
    @55
    @120
    @55
    c2
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    @120
    cn
    wcel
    #
    2nn
    wph
    @54
    @127
    @51
    4sq.2
    3ad2ant1
    #
    c2
    cN
    nnmulcl
    sylancr
    #
    nnred
    resqcld
    #
    @55
    @122
    @55
    @126
    @128
    @122
    cn
    wcel
    2nn
    @130
    c2
    @120
    nnmulcl
    sylancr
    #
    nnred
    readdcld
    #
    @55
    1red
    @55
    @56
    @121
    @123
    @125
    @131
    @133
    @55
    @56
    c2
    cN
    c2
    cexp
    co
    #
    cmul
    co
    #
    @121
    @125
    @55
    @135
    @55
    @126
    @134
    cn
    wcel
    @135
    cn
    wcel
    2nn
    @55
    cN
    @129
    nnsqcld
    #
    c2
    @134
    nnmulcl
    sylancr
    nnred
    @131
    @55
    @56
    @134
    @134
    caddc
    co
    @135
    cle
    @55
    @16
    @20
    @134
    @134
    @55
    @16
    @108
    nn0red
    @100
    @55
    @134
    @136
    nnred
    #
    @137
    @55
    @15
    cr
    wcel
    cc0
    @15
    cle
    wbr
    #
    cN
    cr
    wcel
    #
    @15
    cN
    cle
    wbr
    #
    @16
    @134
    cle
    wbr
    @55
    @15
    @107
    zred
    #
    @55
    @52
    @138
    @106
    @15
    cc0
    cN
    elfzle1
    syl
    @55
    cN
    @129
    nnred
    #
    @55
    @52
    @140
    @106
    @15
    cc0
    cN
    elfzle2
    syl
    @15
    cN
    le2sq2
    syl22anc
    @55
    @19
    cr
    wcel
    cc0
    @19
    cle
    wbr
    #
    @139
    @19
    cN
    cle
    wbr
    #
    @20
    @134
    cle
    wbr
    @55
    @19
    @98
    zred
    #
    @55
    @53
    @143
    @97
    @19
    cc0
    cN
    elfzle1
    syl
    @142
    @55
    @53
    @144
    @97
    @19
    cc0
    cN
    elfzle2
    syl
    @19
    cN
    le2sq2
    syl22anc
    le2addd
    @55
    @134
    @55
    @134
    @136
    nncnd
    2timesd
    breqtrrd
    @55
    @135
    c4
    @134
    cmul
    co
    #
    @121
    clt
    @55
    c2
    c4
    clt
    wbr
    #
    @135
    @146
    clt
    wbr
    #
    2lt4
    @55
    c2
    cr
    wcel
    #
    c4
    cr
    wcel
    #
    @134
    cr
    wcel
    cc0
    @134
    clt
    wbr
    @147
    @148
    wb
    @149
    @55
    2re
    a1i
    @150
    @55
    4re
    a1i
    @137
    @55
    @134
    @136
    nngt0d
    c2
    c4
    @134
    ltmul1
    syl112anc
    mpbii
    @55
    @121
    c2
    c2
    cexp
    co
    #
    @134
    cmul
    co
    #
    @146
    @55
    c2
    cc
    wcel
    cN
    cc
    wcel
    @121
    @152
    wceq
    2cn
    @55
    cN
    @129
    nncnd
    c2
    cN
    sqmul
    sylancr
    @151
    c4
    @134
    cmul
    sq2
    oveq1i
    syl6eq
    breqtrrd
    lelttrd
    @55
    @121
    @122
    @131
    @55
    @122
    @132
    nnrpd
    ltaddrpd
    lttrd
    ltadd1dd
    @55
    cP
    c2
    cexp
    co
    @120
    c1
    caddc
    co
    #
    c2
    cexp
    co
    #
    @118
    @124
    @55
    cP
    @153
    c2
    cexp
    wph
    @54
    cP
    @153
    wceq
    @51
    4sq.3
    3ad2ant1
    oveq1d
    @55
    cP
    @110
    sqvald
    @55
    @120
    cc
    wcel
    @154
    @124
    wceq
    @55
    @120
    @130
    nncnd
    @120
    binom21
    syl
    3eqtr3d
    breqtrrd
    @55
    @57
    cr
    wcel
    cP
    cr
    wcel
    #
    @155
    cc0
    cP
    clt
    wbr
    @69
    @119
    wb
    @55
    @57
    @113
    nnred
    @89
    @89
    @55
    cP
    @85
    nngt0d
    @57
    cP
    cP
    ltdivmul
    syl112anc
    mpbird
    @55
    c1
    cz
    wcel
    @101
    @59
    @67
    @68
    @69
    w3a
    wb
    1z
    @103
    @58
    c1
    cP
    elfzm11
    sylancr
    mpbir3and
    @55
    @105
    @96
    @61
    @107
    @98
    @15
    @19
    gzreim
    syl2anc
    #
    @55
    @64
    @57
    @65
    @55
    @63
    @56
    c1
    caddc
    @55
    @63
    @60
    cre
    cfv
    #
    c2
    cexp
    co
    #
    @60
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    @56
    @55
    @60
    @55
    @61
    @60
    cc
    wcel
    @156
    @60
    gzcn
    syl
    absvalsq2d
    @55
    @158
    @16
    @160
    @20
    caddc
    @55
    @157
    @15
    c2
    cexp
    @55
    @15
    @19
    @141
    @145
    crred
    oveq1d
    @55
    @159
    @19
    c2
    cexp
    @55
    @15
    @19
    @141
    @145
    crimd
    oveq1d
    oveq12d
    eqtrd
    oveq1d
    @55
    @57
    cP
    @55
    @57
    @113
    nncnd
    @110
    @115
    divcan1d
    eqtr4d
    @11
    @66
    @8
    @65
    wceq
    vk
    vu
    @58
    @60
    @13
    cgz
    @9
    @58
    wceq
    @10
    @65
    @8
    @9
    @58
    cP
    cmul
    oveq1
    eqeq2d
    @5
    @60
    wceq
    #
    @8
    @64
    @65
    @161
    @7
    @63
    c1
    caddc
    @161
    @6
    @62
    c2
    cexp
    @5
    @60
    cabs
    fveq2
    oveq1d
    oveq1d
    eqeq1d
    rspc2ev
    syl3anc
    3expia
    syl5
    rexlimdvva
    syl5bi
    exlimdv
    mpd
end
