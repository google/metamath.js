include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "c2.mm"
include "cneg.mm"
include "cexp.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "caddc.mm"
include "c1.mm"
include "simpl3.mm"
include "nnred.mm"
include "resqcld.mm"
include "sqge0d.mm"
include "absidd.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "simpl2.mm"
include "nncnd.mm"
include "sqcld.mm"
include "simpl1.mm"
include "mulcld.mm"
include "subcld.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0d.mm"
include "sqne0.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "absdivd.mm"
include "eqtr4d.mm"
include "abscld.mm"
include "recnd.mm"
include "divcan2d.mm"
include "divsubdird.mm"
include "sqdivd.mm"
include "cr.mm"
include "cle.mm"
include "wceq.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "remsqsqrt.mm"
include "resqrtcld.mm"
include "sqvald.mm"
include "divcan4d.mm"
include "3eqtr4rd.mm"
include "oveq12d.mm"
include "divcld.mm"
include "subsq.mm"
include "addcld.mm"
include "nndivred.mm"
include "resubcld.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "absmuld.mm"
include "remulcld.mm"
include "cz.mm"
include "2nn0.mm"
include "nn0negzi.mm"
include "a1i.mm"
include "reexpclzd.mm"
include "1red.mm"
include "2re.mm"
include "readdcld.mm"
include "simpr.mm"
include "wb.mm"
include "nngt0d.mm"
include "divgt0d.mm"
include "sqrtgt0.mm"
include "addgt0d.mm"
include "gt0ne0d.mm"
include "absgt0.mm"
include "biimpa.mm"
include "ltmul1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "sqgt0d.mm"
include "ltmul2.mm"
include "expclzd.mm"
include "mulass.mm"
include "syl3anc.mm"
include "cn0.mm"
include "expneg.mm"
include "sylancl.mm"
include "recidd.mm"
include "oveq1d.mm"
include "mulid2d.mm"
include "addcomd.mm"
include "ppncan.mm"
include "2times.mm"
include "syl.mm"
include "abstrid.mm"
include "0le2.mm"
include "sqrtge0d.mm"
include "mulge0d.mm"
include "nnsqcld.mm"
include "nnge1d.mm"
include "0lt1.mm"
include "lerec.mm"
include "syl22anc.mm"
include "1div1e1.mm"
include "syl6breq.mm"
include "eqbrtrd.mm"
include "ltletrd.mm"
include "ltled.mm"
include "leadd1dd.mm"
include "letrd.mm"

theorem pellexlem2
  let cA: class A
  let cB: class B
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let cC: class C
  let cE: class E
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph


  assert |- ( ( ( D e. NN /\ A e. NN /\ B e. NN ) /\ ( abs ` ( ( A / B ) - ( sqrt ` D ) ) ) < ( B ^ -u 2 ) ) -> ( abs ` ( ( A ^ 2 ) - ( D x. ( B ^ 2 ) ) ) ) < ( 1 + ( 2 x. ( sqrt ` D ) ) ) )

  proof
    cD
    cn
    wcel
    #
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    w3a
    #
    cA
    cB
    cdiv
    co
    #
    cD
    csqrt
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cB
    c2
    cneg
    #
    cexp
    co
    #
    clt
    wbr
    #
    wa
    #
    cA
    c2
    cexp
    co
    #
    cD
    cB
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    @6
    @4
    @5
    caddc
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    c1
    c2
    @5
    cmul
    co
    #
    caddc
    co
    #
    clt
    @11
    @13
    @16
    @13
    cdiv
    co
    #
    cmul
    co
    @13
    @15
    @13
    cdiv
    co
    #
    cabs
    cfv
    #
    cmul
    co
    @16
    @20
    @11
    @23
    @25
    @13
    cmul
    @11
    @23
    @16
    @13
    cabs
    cfv
    #
    cdiv
    co
    @25
    @11
    @13
    @26
    @16
    cdiv
    @11
    @26
    @13
    @11
    @13
    @11
    cB
    @11
    cB
    @0
    @1
    @2
    @10
    simpl3
    #
    nnred
    #
    resqcld
    #
    @11
    cB
    @28
    sqge0d
    absidd
    eqcomd
    oveq2d
    @11
    @15
    @13
    @11
    @12
    @14
    @11
    cA
    @11
    cA
    @0
    @1
    @2
    @10
    simpl2
    #
    nncnd
    #
    sqcld
    #
    @11
    cD
    @13
    @11
    cD
    @0
    @1
    @2
    @10
    simpl1
    #
    nncnd
    #
    @11
    cB
    @11
    cB
    @27
    nncnd
    #
    sqcld
    #
    mulcld
    #
    subcld
    #
    @36
    @11
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    @13
    cc0
    wne
    #
    @35
    @11
    cB
    @27
    nnne0d
    #
    @39
    @41
    @40
    cB
    sqne0
    biimpar
    syl2anc
    #
    absdivd
    eqtr4d
    oveq2d
    @11
    @16
    @13
    @11
    @16
    @11
    @15
    @38
    abscld
    recnd
    @36
    @43
    divcan2d
    @11
    @25
    @19
    @13
    cmul
    @11
    @24
    @18
    cabs
    @11
    @24
    @12
    @13
    cdiv
    co
    #
    @14
    @13
    cdiv
    co
    #
    cmin
    co
    @4
    c2
    cexp
    co
    #
    @5
    c2
    cexp
    co
    #
    cmin
    co
    #
    @18
    @11
    @12
    @14
    @13
    @32
    @37
    @36
    @43
    divsubdird
    @11
    @44
    @46
    @45
    @47
    cmin
    @11
    @46
    @44
    @11
    cA
    cB
    @31
    @35
    @42
    sqdivd
    eqcomd
    @11
    @5
    @5
    cmul
    co
    #
    cD
    @47
    @45
    @11
    cD
    cr
    wcel
    #
    cc0
    cD
    cle
    wbr
    @49
    cD
    wceq
    @11
    cD
    @33
    nnred
    #
    @11
    cD
    @11
    cD
    @33
    nnnn0d
    nn0ge0d
    #
    cD
    remsqsqrt
    syl2anc
    @11
    @5
    @11
    @5
    @11
    cD
    @51
    @52
    resqrtcld
    #
    recnd
    #
    sqvald
    @11
    cD
    @13
    @34
    @36
    @43
    divcan4d
    3eqtr4rd
    oveq12d
    @11
    @48
    @17
    @6
    cmul
    co
    #
    @18
    @11
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @48
    @55
    wceq
    @11
    cA
    cB
    @31
    @35
    @42
    divcld
    #
    @54
    @4
    @5
    subsq
    syl2anc
    @11
    @17
    @6
    @11
    @4
    @5
    @58
    @54
    addcld
    #
    @11
    @6
    @11
    @4
    @5
    @11
    cA
    cB
    @11
    cA
    @30
    nnred
    #
    @27
    nndivred
    #
    @53
    resubcld
    #
    recnd
    #
    mulcomd
    eqtrd
    3eqtrd
    fveq2d
    oveq2d
    3eqtr3d
    @11
    @20
    @13
    @7
    @17
    cabs
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    @22
    clt
    @11
    @19
    @65
    @13
    cmul
    @11
    @6
    @17
    @63
    @59
    absmuld
    oveq2d
    @11
    @66
    @13
    @9
    @64
    cmul
    co
    #
    cmul
    co
    #
    @22
    @11
    @13
    @65
    @29
    @11
    @7
    @64
    @11
    @6
    @63
    abscld
    #
    @11
    @17
    @59
    abscld
    #
    remulcld
    #
    remulcld
    @11
    @13
    @67
    @29
    @11
    @9
    @64
    @11
    cB
    @8
    @28
    @42
    @8
    cz
    wcel
    @11
    c2
    2nn0
    nn0negzi
    a1i
    #
    reexpclzd
    #
    @70
    remulcld
    #
    remulcld
    @11
    c1
    @21
    @11
    1red
    #
    @11
    c2
    @5
    c2
    cr
    wcel
    @11
    2re
    a1i
    #
    @53
    remulcld
    #
    readdcld
    #
    @11
    @65
    @67
    clt
    wbr
    #
    @66
    @68
    clt
    wbr
    #
    @11
    @10
    @79
    @3
    @10
    simpr
    #
    @11
    @7
    cr
    wcel
    @9
    cr
    wcel
    @64
    cr
    wcel
    cc0
    @64
    clt
    wbr
    #
    @10
    @79
    wb
    @69
    @73
    @70
    @11
    @17
    cc
    wcel
    #
    @17
    cc0
    wne
    #
    @82
    @59
    @11
    @17
    @11
    @4
    @5
    @61
    @53
    @11
    cA
    cB
    @60
    @28
    @11
    cA
    @30
    nngt0d
    @11
    cB
    @27
    nngt0d
    divgt0d
    @11
    @50
    cc0
    cD
    clt
    wbr
    cc0
    @5
    clt
    wbr
    @51
    @11
    cD
    @33
    nngt0d
    cD
    sqrtgt0
    syl2anc
    addgt0d
    gt0ne0d
    @83
    @84
    @82
    @17
    absgt0
    biimpa
    syl2anc
    @7
    @9
    @64
    ltmul1
    syl112anc
    mpbid
    @11
    @65
    cr
    wcel
    @67
    cr
    wcel
    @13
    cr
    wcel
    #
    cc0
    @13
    clt
    wbr
    #
    @79
    @80
    wb
    @71
    @74
    @29
    @11
    cB
    @28
    @42
    sqgt0d
    #
    @65
    @67
    @13
    ltmul2
    syl112anc
    mpbid
    @11
    @68
    @64
    @22
    cle
    @11
    @68
    @13
    @9
    cmul
    co
    #
    @64
    cmul
    co
    #
    c1
    @64
    cmul
    co
    @64
    @11
    @13
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    @64
    cc
    wcel
    #
    @68
    @89
    wceq
    @36
    @11
    cB
    @8
    @35
    @42
    @72
    expclzd
    @11
    @64
    @70
    recnd
    #
    @90
    @91
    @92
    w3a
    @89
    @68
    @13
    @9
    @64
    mulass
    eqcomd
    syl3anc
    @11
    @88
    c1
    @64
    cmul
    @11
    @88
    @13
    c1
    @13
    cdiv
    co
    #
    cmul
    co
    c1
    @11
    @9
    @94
    @13
    cmul
    @11
    @39
    c2
    cn0
    wcel
    @9
    @94
    wceq
    @35
    2nn0
    cB
    c2
    expneg
    sylancl
    #
    oveq2d
    @11
    @13
    @36
    @43
    recidd
    eqtrd
    oveq1d
    @11
    @64
    @93
    mulid2d
    3eqtrd
    @11
    @64
    @6
    @21
    caddc
    co
    #
    cabs
    cfv
    #
    @22
    cle
    @11
    @17
    @96
    cabs
    @11
    @17
    @5
    @4
    caddc
    co
    #
    @5
    @5
    caddc
    co
    #
    @6
    caddc
    co
    #
    @96
    @11
    @4
    @5
    @58
    @54
    addcomd
    @11
    @57
    @57
    @56
    @98
    @100
    wceq
    @54
    @54
    @58
    @57
    @57
    @56
    w3a
    @100
    @98
    @5
    @5
    @4
    ppncan
    eqcomd
    syl3anc
    @11
    @100
    @6
    @99
    caddc
    co
    @96
    @11
    @99
    @6
    @11
    @5
    @5
    @54
    @54
    addcld
    @63
    addcomd
    @11
    @99
    @21
    @6
    caddc
    @11
    @57
    @99
    @21
    wceq
    @54
    @57
    @21
    @99
    @5
    2times
    eqcomd
    syl
    oveq2d
    eqtrd
    3eqtrd
    fveq2d
    @11
    @97
    @7
    @21
    cabs
    cfv
    #
    caddc
    co
    #
    @22
    @11
    @96
    @11
    @96
    @11
    @6
    @21
    @62
    @77
    readdcld
    recnd
    abscld
    @11
    @7
    @101
    @69
    @11
    @21
    @11
    @21
    @77
    recnd
    #
    abscld
    readdcld
    @78
    @11
    @6
    @21
    @63
    @103
    abstrid
    @11
    @102
    @7
    @21
    caddc
    co
    @22
    cle
    @11
    @101
    @21
    @7
    caddc
    @11
    @21
    @77
    @11
    c2
    @5
    @76
    @53
    cc0
    c2
    cle
    wbr
    @11
    0le2
    a1i
    @11
    cD
    @51
    @52
    sqrtge0d
    mulge0d
    absidd
    oveq2d
    @11
    @7
    c1
    @21
    @69
    @75
    @77
    @11
    @7
    c1
    @69
    @75
    @11
    @7
    @9
    c1
    @69
    @73
    @75
    @81
    @11
    @9
    @94
    c1
    cle
    @95
    @11
    @94
    c1
    c1
    cdiv
    co
    #
    c1
    cle
    @11
    c1
    @13
    cle
    wbr
    #
    @94
    @104
    cle
    wbr
    #
    @11
    @13
    @11
    cB
    @27
    nnsqcld
    nnge1d
    @11
    c1
    cr
    wcel
    cc0
    c1
    clt
    wbr
    #
    @85
    @86
    @105
    @106
    wb
    @75
    @107
    @11
    0lt1
    a1i
    @29
    @87
    c1
    @13
    lerec
    syl22anc
    mpbid
    1div1e1
    syl6breq
    eqbrtrd
    ltletrd
    ltled
    leadd1dd
    eqbrtrd
    letrd
    eqbrtrd
    eqbrtrd
    ltletrd
    eqbrtrd
    eqbrtrd
end
