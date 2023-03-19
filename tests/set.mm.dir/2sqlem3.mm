include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cgz.mm"
include "wrex.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "caddc.mm"
include "cdiv.mm"
include "cc.mm"
include "cre.mm"
include "cz.mm"
include "cim.mm"
include "gzreim.mm"
include "syl2anc.mm"
include "gzmulcl.mm"
include "gzcn.mm"
include "syl.mm"
include "cprime.mm"
include "cn.mm"
include "prmnn.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "nnred.mm"
include "redivd.mm"
include "cdvds.mm"
include "wbr.mm"
include "prmz.mm"
include "dvdsmul2.mm"
include "sqvald.mm"
include "breqtrrd.mm"
include "nnzd.mm"
include "zsqcl.mm"
include "wa.mm"
include "wi.mm"
include "zmulcld.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "abscld.mm"
include "recnd.mm"
include "sqmuld.mm"
include "zred.mm"
include "crred.mm"
include "oveq1d.mm"
include "crimd.mm"
include "oveq12d.mm"
include "absvalsq2d.mm"
include "3eqtr4d.mm"
include "mulassd.mm"
include "3eqtrd.mm"
include "absmuld.mm"
include "oveq2d.mm"
include "elgz.mm"
include "simp2bi.mm"
include "zcnd.mm"
include "simp3bi.mm"
include "addcomd.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "wb.mm"
include "mulcld.mm"
include "mulcomd.mm"
include "immuld.mm"
include "2nn.mm"
include "a1i.mm"
include "prmdvdsexp.mm"
include "mpbird.mm"
include "dvdsadd2b.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "cc0.mm"
include "wne.mm"
include "dvdsval2.mm"
include "eqeltrd.mm"
include "imdivd.mm"
include "syl3anbrc.mm"
include "absdivd.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "sqdivd.mm"
include "nnsqcld.mm"
include "divcan4d.mm"
include "3eqtrrd.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "2sqlem1.mm"
include "sylibr.mm"

theorem 2sqlem3
  let wph: wff ph
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vu: setvar u
  let vv: setvar v
  let cM: class M
  let cE: class E
  let cY: class Y
  let cF: class F
  assume 2sq.1: |- S = ran ( w e. Z[i] |-> ( ( abs ` w ) ^ 2 ) )
  assume 2sqlem5.1: |- ( ph -> N e. NN )
  assume 2sqlem5.2: |- ( ph -> P e. Prime )
  assume 2sqlem4.3: |- ( ph -> A e. ZZ )
  assume 2sqlem4.4: |- ( ph -> B e. ZZ )
  assume 2sqlem4.5: |- ( ph -> C e. ZZ )
  assume 2sqlem4.6: |- ( ph -> D e. ZZ )
  assume 2sqlem4.7: |- ( ph -> ( N x. P ) = ( ( A ^ 2 ) + ( B ^ 2 ) ) )
  assume 2sqlem4.8: |- ( ph -> P = ( ( C ^ 2 ) + ( D ^ 2 ) ) )
  assume 2sqlem4.9: |- ( ph -> P || ( ( C x. B ) + ( A x. D ) ) )


  assert |- ( ph -> N e. S )

  proof
    wph
    cN
    vx
    cv
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    #
    vx
    cgz
    wrex
    #
    cN
    cS
    wcel
    wph
    cA
    ci
    cB
    cmul
    co
    caddc
    co
    #
    cC
    ci
    cD
    cmul
    co
    caddc
    co
    #
    cmul
    co
    #
    cP
    cdiv
    co
    #
    cgz
    wcel
    #
    cN
    @8
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    #
    @4
    wph
    @8
    cc
    wcel
    @8
    cre
    cfv
    #
    cz
    wcel
    @8
    cim
    cfv
    #
    cz
    wcel
    @9
    wph
    @7
    cP
    wph
    @7
    cgz
    wcel
    #
    @7
    cc
    wcel
    #
    wph
    @5
    cgz
    wcel
    #
    @6
    cgz
    wcel
    #
    @15
    wph
    cA
    cz
    wcel
    cB
    cz
    wcel
    @17
    2sqlem4.3
    2sqlem4.4
    cA
    cB
    gzreim
    syl2anc
    #
    wph
    cC
    cz
    wcel
    cD
    cz
    wcel
    @18
    2sqlem4.5
    2sqlem4.6
    cC
    cD
    gzreim
    syl2anc
    #
    @5
    @6
    gzmulcl
    syl2anc
    #
    @7
    gzcn
    syl
    #
    wph
    cP
    wph
    cP
    cprime
    wcel
    #
    cP
    cn
    wcel
    2sqlem5.2
    cP
    prmnn
    syl
    #
    nncnd
    #
    wph
    cP
    @24
    nnne0d
    #
    divcld
    wph
    @13
    @7
    cre
    cfv
    #
    cP
    cdiv
    co
    #
    cz
    wph
    cP
    @7
    wph
    cP
    @24
    nnred
    #
    @22
    @26
    redivd
    wph
    cP
    @27
    cdvds
    wbr
    #
    @28
    cz
    wcel
    #
    wph
    cP
    @27
    c2
    cexp
    co
    #
    cdvds
    wbr
    #
    @30
    wph
    @33
    cP
    @7
    cim
    cfv
    #
    c2
    cexp
    co
    #
    @32
    caddc
    co
    #
    cdvds
    wbr
    #
    wph
    cP
    @7
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @36
    cdvds
    wph
    cP
    cN
    cP
    c2
    cexp
    co
    #
    cmul
    co
    #
    @39
    cdvds
    wph
    cP
    @40
    cdvds
    wbr
    #
    @40
    @41
    cdvds
    wbr
    #
    cP
    @41
    cdvds
    wbr
    #
    wph
    cP
    cP
    cP
    cmul
    co
    #
    @40
    cdvds
    wph
    cP
    cz
    wcel
    #
    @46
    cP
    @45
    cdvds
    wbr
    wph
    @23
    @46
    2sqlem5.2
    cP
    prmz
    syl
    #
    @47
    cP
    cP
    dvdsmul2
    syl2anc
    wph
    cP
    @25
    sqvald
    #
    breqtrrd
    wph
    cN
    cz
    wcel
    @40
    cz
    wcel
    #
    @43
    wph
    cN
    2sqlem5.1
    nnzd
    #
    wph
    @46
    @49
    @47
    cP
    zsqcl
    syl
    #
    cN
    @40
    dvdsmul2
    syl2anc
    wph
    @46
    @49
    @41
    cz
    wcel
    @42
    @43
    wa
    @44
    wi
    @47
    @51
    wph
    cN
    @40
    @50
    @51
    zmulcld
    cP
    @40
    @41
    dvdstr
    syl3anc
    mp2and
    wph
    @5
    cabs
    cfv
    #
    @6
    cabs
    cfv
    #
    cmul
    co
    #
    c2
    cexp
    co
    #
    cN
    @45
    cmul
    co
    #
    @39
    @41
    wph
    @55
    @52
    c2
    cexp
    co
    #
    @53
    c2
    cexp
    co
    #
    cmul
    co
    cN
    cP
    cmul
    co
    #
    cP
    cmul
    co
    @56
    wph
    @52
    @53
    wph
    @52
    wph
    @5
    wph
    @17
    @5
    cc
    wcel
    @19
    @5
    gzcn
    syl
    #
    abscld
    recnd
    wph
    @53
    wph
    @6
    wph
    @18
    @6
    cc
    wcel
    @20
    @6
    gzcn
    syl
    #
    abscld
    recnd
    sqmuld
    wph
    @57
    @59
    @58
    cP
    cmul
    wph
    @5
    cre
    cfv
    #
    c2
    cexp
    co
    #
    @5
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    @57
    @59
    wph
    @63
    @66
    @65
    @67
    caddc
    wph
    @62
    cA
    c2
    cexp
    wph
    cA
    cB
    wph
    cA
    2sqlem4.3
    zred
    #
    wph
    cB
    2sqlem4.4
    zred
    #
    crred
    #
    oveq1d
    wph
    @64
    cB
    c2
    cexp
    wph
    cA
    cB
    @68
    @69
    crimd
    #
    oveq1d
    oveq12d
    wph
    @5
    @60
    absvalsq2d
    2sqlem4.7
    3eqtr4d
    wph
    @6
    cre
    cfv
    #
    c2
    cexp
    co
    #
    @6
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    cC
    c2
    cexp
    co
    #
    cD
    c2
    cexp
    co
    #
    caddc
    co
    @58
    cP
    wph
    @73
    @76
    @75
    @77
    caddc
    wph
    @72
    cC
    c2
    cexp
    wph
    cC
    cD
    wph
    cC
    2sqlem4.5
    zred
    #
    wph
    cD
    2sqlem4.6
    zred
    #
    crred
    #
    oveq1d
    wph
    @74
    cD
    c2
    cexp
    wph
    cC
    cD
    @78
    @79
    crimd
    #
    oveq1d
    oveq12d
    wph
    @6
    @61
    absvalsq2d
    2sqlem4.8
    3eqtr4d
    oveq12d
    wph
    cN
    cP
    cP
    wph
    cN
    2sqlem5.1
    nncnd
    #
    @25
    @25
    mulassd
    3eqtrd
    wph
    @38
    @54
    c2
    cexp
    wph
    @5
    @6
    @60
    @61
    absmuld
    oveq1d
    wph
    @40
    @45
    cN
    cmul
    @48
    oveq2d
    3eqtr4d
    #
    breqtrrd
    wph
    @39
    @32
    @35
    caddc
    co
    @36
    wph
    @7
    @22
    absvalsq2d
    wph
    @32
    @35
    wph
    @32
    wph
    @27
    cz
    wcel
    #
    @32
    cz
    wcel
    #
    wph
    @15
    @84
    @21
    @15
    @16
    @84
    @34
    cz
    wcel
    #
    @7
    elgz
    #
    simp2bi
    syl
    #
    @27
    zsqcl
    syl
    #
    zcnd
    wph
    @35
    wph
    @86
    @35
    cz
    wcel
    #
    wph
    @15
    @86
    @21
    @15
    @16
    @84
    @86
    @87
    simp3bi
    syl
    #
    @34
    zsqcl
    syl
    #
    zcnd
    addcomd
    eqtrd
    breqtrd
    wph
    @46
    @85
    @90
    cP
    @35
    cdvds
    wbr
    #
    @33
    @37
    wb
    @47
    @89
    @92
    wph
    @93
    cP
    @34
    cdvds
    wbr
    #
    wph
    cP
    cA
    cD
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    caddc
    co
    #
    @34
    cdvds
    wph
    cP
    cC
    cB
    cmul
    co
    #
    @95
    caddc
    co
    #
    @97
    cdvds
    2sqlem4.9
    wph
    @99
    @95
    @98
    caddc
    co
    @97
    wph
    @98
    @95
    wph
    cC
    cB
    wph
    cC
    2sqlem4.5
    zcnd
    #
    wph
    cB
    2sqlem4.4
    zcnd
    #
    mulcld
    wph
    cA
    cD
    wph
    cA
    2sqlem4.3
    zcnd
    wph
    cD
    2sqlem4.6
    zcnd
    mulcld
    addcomd
    wph
    @98
    @96
    @95
    caddc
    wph
    cC
    cB
    @100
    @101
    mulcomd
    oveq2d
    eqtrd
    breqtrd
    wph
    @34
    @62
    @74
    cmul
    co
    #
    @64
    @72
    cmul
    co
    #
    caddc
    co
    @97
    wph
    @5
    @6
    @60
    @61
    immuld
    wph
    @102
    @95
    @103
    @96
    caddc
    wph
    @62
    cA
    @74
    cD
    cmul
    @70
    @81
    oveq12d
    wph
    @64
    cB
    @72
    cC
    cmul
    @71
    @80
    oveq12d
    oveq12d
    eqtrd
    breqtrrd
    #
    wph
    @23
    @86
    c2
    cn
    wcel
    #
    @93
    @94
    wb
    2sqlem5.2
    @91
    @105
    wph
    2nn
    a1i
    #
    @34
    cP
    c2
    prmdvdsexp
    syl3anc
    mpbird
    cP
    @32
    @35
    dvdsadd2b
    syl112anc
    mpbird
    wph
    @23
    @84
    @105
    @33
    @30
    wb
    2sqlem5.2
    @88
    @106
    @27
    cP
    c2
    prmdvdsexp
    syl3anc
    mpbid
    wph
    @46
    cP
    cc0
    wne
    #
    @84
    @30
    @31
    wb
    @47
    @26
    @88
    cP
    @27
    dvdsval2
    syl3anc
    mpbid
    eqeltrd
    wph
    @14
    @34
    cP
    cdiv
    co
    #
    cz
    wph
    cP
    @7
    @29
    @22
    @26
    imdivd
    wph
    @94
    @108
    cz
    wcel
    #
    @104
    wph
    @46
    @107
    @86
    @94
    @109
    wb
    @47
    @26
    @91
    cP
    @34
    dvdsval2
    syl3anc
    mpbid
    eqeltrd
    @8
    elgz
    syl3anbrc
    wph
    @11
    @38
    cP
    cdiv
    co
    #
    c2
    cexp
    co
    @39
    @40
    cdiv
    co
    #
    cN
    wph
    @10
    @110
    c2
    cexp
    wph
    @10
    @38
    cP
    cabs
    cfv
    #
    cdiv
    co
    @110
    wph
    @7
    cP
    @22
    @25
    @26
    absdivd
    wph
    @112
    cP
    @38
    cdiv
    wph
    cP
    @29
    wph
    cP
    wph
    cP
    @24
    nnnn0d
    nn0ge0d
    absidd
    oveq2d
    eqtrd
    oveq1d
    wph
    @38
    cP
    wph
    @38
    wph
    @7
    @22
    abscld
    recnd
    @25
    @26
    sqdivd
    wph
    @111
    @41
    @40
    cdiv
    co
    cN
    wph
    @39
    @41
    @40
    cdiv
    @83
    oveq1d
    wph
    cN
    @40
    @82
    wph
    @40
    wph
    cP
    @24
    nnsqcld
    #
    nncnd
    wph
    @40
    @113
    nnne0d
    divcan4d
    eqtrd
    3eqtrrd
    @3
    @12
    vx
    @8
    cgz
    @0
    @8
    wceq
    #
    @2
    @11
    cN
    @114
    @1
    @10
    c2
    cexp
    @0
    @8
    cabs
    fveq2
    oveq1d
    eqeq2d
    rspcev
    syl2anc
    vx
    vw
    cN
    cS
    2sq.1
    2sqlem1
    sylibr
end
