include "cv.mm"
include "cfv.mm"
include "chio.mm"
include "cleo.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "ch0o.mm"
include "opsqrlem2.mm"
include "idleop.mm"
include "eqbrtri.mm"
include "cn.mm"
include "wcel.mm"
include "chod.mm"
include "c2.mm"
include "chot.mm"
include "ccom.mm"
include "chos.mm"
include "cho.mm"
include "idhmop.mm"
include "opsqrlem4.mm"
include "ffvelrni.mm"
include "hmopd.mm"
include "sylancr.mm"
include "eqid.mm"
include "hmopco.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "leopsq.mm"
include "syl.mm"
include "wb.mm"
include "leop3.mm"
include "mp2an.mm"
include "mpbi.mm"
include "wa.mm"
include "leopadd.mm"
include "mpanl2.mm"
include "mpanr2.mm"
include "cdiv.mm"
include "chil.mm"
include "wf.mm"
include "cc.mm"
include "2cn.mm"
include "hmopf.mm"
include "homulcl.mm"
include "ax-mp.mm"
include "fco.mm"
include "hosubcl.mm"
include "hosubsub4.mm"
include "mp3an1.mm"
include "hoadd32.mm"
include "mp3an13.mm"
include "ho2times.mm"
include "oveq1i.mm"
include "syl6eqr.mm"
include "hoaddsubass.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "hoaddcl.mm"
include "mp3an23.mm"
include "3eqtr3d.mm"
include "hosubadd4.mm"
include "mpanr1.mm"
include "mpanl1.mm"
include "halfcn.mm"
include "hoadddi.mm"
include "cmul.mm"
include "2ne0.mm"
include "recidi.mm"
include "homulass.mm"
include "mp3an12.mm"
include "homulid2.mm"
include "3eqtr3a.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "hosubdi.mm"
include "hocsubdir.mm"
include "clo.mm"
include "hmoplin.mm"
include "hoddi.mm"
include "hoid1i.mm"
include "a1i.mm"
include "hoico2.mm"
include "oveq12d.mm"
include "mp3an2.mm"
include "hoico1.mm"
include "jctil.mm"
include "syl12anc.mm"
include "3eqtr2d.mm"
include "opsqrlem5.mm"
include "breqtrd.mm"
include "peano2nn.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "2re.mm"
include "2pos.mm"
include "leopmul.mm"
include "mpbird.mm"
include "sylancl.mm"
include "nn1suc.mm"

theorem opsqrlem6
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  let cF: class F
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vz: setvar z
  let cG: class G
  let cH: class H
  assume opsqrlem2.1: |- T e. HrmOp
  assume opsqrlem2.2: |- S = ( x e. HrmOp , y e. HrmOp |-> ( x +op ( ( 1 / 2 ) .op ( T -op ( x o. x ) ) ) ) )
  assume opsqrlem2.3: |- F = seq 1 ( S , ( NN X. { 0hop } ) )
  assume opsqrlem6.4: |- T <_op Iop

  disjoint x y
  disjoint T x
  disjoint T y
  disjoint j k
  disjoint F j
  disjoint F k
  disjoint w z
  disjoint G w
  disjoint G z
  disjoint N j
  disjoint N k
  disjoint S w
  disjoint S z
  disjoint w x
  disjoint w y
  disjoint T w
  disjoint x z
  disjoint y z
  disjoint T z
  disjoint H w
  disjoint H z
  assert |- ( N e. NN -> ( F ` N ) <_op Iop )

  proof
    vj
    cv
    #
    cF
    cfv
    #
    chio
    cleo
    wbr
    c1
    cF
    cfv
    #
    chio
    cleo
    wbr
    vk
    cv
    #
    c1
    caddc
    co
    #
    cF
    cfv
    #
    chio
    cleo
    wbr
    #
    cN
    cF
    cfv
    #
    chio
    cleo
    wbr
    vj
    vk
    cN
    @0
    c1
    wceq
    @1
    @2
    chio
    cleo
    @0
    c1
    cF
    fveq2
    breq1d
    @0
    @4
    wceq
    @1
    @5
    chio
    cleo
    @0
    @4
    cF
    fveq2
    breq1d
    @0
    cN
    wceq
    @1
    @7
    chio
    cleo
    @0
    cN
    cF
    fveq2
    breq1d
    @2
    ch0o
    chio
    cleo
    vx
    vy
    cS
    cT
    cF
    opsqrlem2.1
    opsqrlem2.2
    opsqrlem2.3
    opsqrlem2
    idleop
    eqbrtri
    @3
    cn
    wcel
    #
    @6
    ch0o
    chio
    @5
    chod
    co
    #
    cleo
    wbr
    #
    @8
    @10
    ch0o
    c2
    @9
    chot
    co
    #
    cleo
    wbr
    #
    @8
    ch0o
    chio
    @3
    cF
    cfv
    #
    chod
    co
    #
    @14
    ccom
    #
    chio
    cT
    chod
    co
    #
    chos
    co
    #
    @11
    cleo
    @8
    @15
    cho
    wcel
    #
    ch0o
    @15
    cleo
    wbr
    #
    ch0o
    @17
    cleo
    wbr
    #
    @8
    @14
    cho
    wcel
    #
    @21
    @18
    @8
    chio
    cho
    wcel
    #
    @13
    cho
    wcel
    #
    @21
    idhmop
    cn
    cho
    @3
    cF
    vx
    vy
    cS
    cT
    cF
    opsqrlem2.1
    opsqrlem2.2
    opsqrlem2.3
    opsqrlem4
    #
    ffvelrni
    #
    chio
    @13
    hmopd
    sylancr
    #
    @26
    @21
    @21
    @15
    @15
    wceq
    @18
    @15
    eqid
    @14
    @14
    hmopco
    mp3an3
    syl2anc
    @8
    @21
    @19
    @26
    @14
    leopsq
    syl
    @18
    @19
    ch0o
    @16
    cleo
    wbr
    #
    @20
    cT
    chio
    cleo
    wbr
    #
    @27
    opsqrlem6.4
    cT
    cho
    wcel
    #
    @22
    @28
    @27
    wb
    opsqrlem2.1
    idhmop
    cT
    chio
    leop3
    mp2an
    mpbi
    @18
    @16
    cho
    wcel
    #
    @19
    @27
    wa
    @20
    @22
    @29
    @30
    idhmop
    opsqrlem2.1
    chio
    cT
    hmopd
    mp2an
    @15
    @16
    leopadd
    mpanl2
    mpanr2
    syl2anc
    @8
    chio
    @13
    @13
    ccom
    #
    c2
    @13
    chot
    co
    #
    chod
    co
    #
    chos
    co
    #
    @16
    chos
    co
    #
    c2
    chio
    @13
    c1
    c2
    cdiv
    co
    #
    cT
    @31
    chod
    co
    #
    chot
    co
    #
    chos
    co
    #
    chod
    co
    #
    chot
    co
    #
    @17
    @11
    @8
    @35
    c2
    chio
    chot
    co
    #
    c2
    @39
    chot
    co
    #
    chod
    co
    #
    @41
    @8
    @42
    @32
    chod
    co
    @37
    chod
    co
    #
    @42
    @32
    @37
    chos
    co
    #
    chod
    co
    #
    @35
    @44
    @8
    chil
    chil
    @32
    wf
    #
    chil
    chil
    @37
    wf
    #
    @45
    @47
    wceq
    #
    @8
    c2
    cc
    wcel
    #
    chil
    chil
    @13
    wf
    #
    @48
    2cn
    @8
    @23
    @52
    @25
    @13
    hmopf
    syl
    #
    c2
    @13
    homulcl
    sylancr
    #
    @8
    chil
    chil
    cT
    wf
    #
    chil
    chil
    @31
    wf
    #
    @49
    @29
    @55
    opsqrlem2.1
    cT
    hmopf
    ax-mp
    #
    @8
    @52
    @52
    @56
    @53
    @53
    chil
    chil
    chil
    @13
    @13
    fco
    syl2anc
    #
    cT
    @31
    hosubcl
    sylancr
    #
    chil
    chil
    @42
    wf
    #
    @48
    @49
    @50
    @51
    chil
    chil
    chio
    wf
    #
    @60
    2cn
    @22
    @61
    idhmop
    chio
    hmopf
    ax-mp
    #
    c2
    chio
    homulcl
    mp2an
    #
    @42
    @32
    @37
    hosubsub4
    mp3an1
    syl2anc
    @8
    @35
    @42
    @31
    chos
    co
    #
    @32
    cT
    chos
    co
    chod
    co
    #
    @45
    @8
    @34
    chio
    chos
    co
    #
    cT
    chod
    co
    #
    @64
    @32
    chod
    co
    #
    cT
    chod
    co
    #
    @35
    @65
    @8
    @66
    @68
    cT
    chod
    @8
    @66
    @42
    @33
    chos
    co
    #
    @68
    @8
    @66
    chio
    chio
    chos
    co
    #
    @33
    chos
    co
    #
    @70
    @8
    chil
    chil
    @33
    wf
    #
    @66
    @72
    wceq
    #
    @8
    @56
    @48
    @73
    @58
    @54
    @31
    @32
    hosubcl
    syl2anc
    #
    @61
    @73
    @61
    @74
    @62
    @62
    chio
    @33
    chio
    hoadd32
    mp3an13
    syl
    @42
    @71
    @33
    chos
    @61
    @42
    @71
    wceq
    @62
    chio
    ho2times
    ax-mp
    oveq1i
    syl6eqr
    @8
    @56
    @48
    @68
    @70
    wceq
    #
    @58
    @54
    @60
    @56
    @48
    @76
    @63
    @42
    @31
    @32
    hoaddsubass
    mp3an1
    syl2anc
    eqtr4d
    oveq1d
    @8
    chil
    chil
    @34
    wf
    #
    @67
    @35
    wceq
    #
    @8
    @61
    @73
    @77
    @62
    @75
    chio
    @33
    hoaddcl
    sylancr
    @77
    @61
    @55
    @78
    @62
    @57
    @34
    chio
    cT
    hoaddsubass
    mp3an23
    syl
    @8
    chil
    chil
    @64
    wf
    #
    @48
    @69
    @65
    wceq
    #
    @8
    @60
    @56
    @79
    @63
    @58
    @42
    @31
    hoaddcl
    sylancr
    @54
    @79
    @48
    @55
    @80
    @57
    @64
    @32
    cT
    hosubsub4
    mp3an3
    syl2anc
    3eqtr3d
    @8
    @48
    @56
    @45
    @65
    wceq
    #
    @54
    @58
    @60
    @48
    @56
    @81
    @63
    @60
    @48
    wa
    @55
    @56
    @81
    @57
    @42
    @32
    cT
    @31
    hosubadd4
    mpanr1
    mpanl1
    syl2anc
    eqtr4d
    @8
    @43
    @46
    @42
    chod
    @8
    @43
    @32
    c2
    @38
    chot
    co
    #
    chos
    co
    #
    @46
    @8
    @52
    chil
    chil
    @38
    wf
    #
    @43
    @83
    wceq
    #
    @53
    @8
    @36
    cc
    wcel
    #
    @49
    @84
    halfcn
    @59
    @36
    @37
    homulcl
    sylancr
    #
    @51
    @52
    @84
    @85
    2cn
    c2
    @13
    @38
    hoadddi
    mp3an1
    syl2anc
    @8
    @82
    @37
    @32
    chos
    @8
    c2
    @36
    cmul
    co
    #
    @37
    chot
    co
    #
    c1
    @37
    chot
    co
    #
    @82
    @37
    @88
    c1
    @37
    chot
    c2
    2cn
    2ne0
    recidi
    oveq1i
    @8
    @49
    @89
    @82
    wceq
    #
    @59
    @51
    @86
    @49
    @91
    2cn
    halfcn
    c2
    @36
    @37
    homulass
    mp3an12
    syl
    @8
    @49
    @90
    @37
    wceq
    @59
    @37
    homulid2
    syl
    3eqtr3a
    oveq2d
    eqtrd
    oveq2d
    3eqtr4d
    @8
    chil
    chil
    @39
    wf
    #
    @41
    @44
    wceq
    #
    @8
    @52
    @84
    @92
    @53
    @87
    @13
    @38
    hoaddcl
    syl2anc
    @51
    @61
    @92
    @93
    2cn
    @62
    c2
    chio
    @39
    hosubdi
    mp3an12
    syl
    eqtr4d
    @8
    @15
    @34
    @16
    chos
    @8
    @15
    chio
    @14
    ccom
    #
    @13
    @14
    ccom
    #
    chod
    co
    #
    @34
    @8
    @52
    chil
    chil
    @14
    wf
    #
    @15
    @96
    wceq
    #
    @53
    @8
    @61
    @52
    @97
    @62
    @53
    chio
    @13
    hosubcl
    sylancr
    @61
    @52
    @97
    @98
    @62
    chio
    @13
    @14
    hocsubdir
    mp3an1
    syl2anc
    @8
    @96
    chio
    @31
    chos
    co
    #
    @13
    @13
    chos
    co
    #
    chod
    co
    #
    @99
    @32
    chod
    co
    #
    @34
    @8
    @96
    @14
    @13
    @31
    chod
    co
    #
    chod
    co
    #
    @101
    @8
    @94
    @14
    @95
    @103
    chod
    @8
    @94
    chio
    chio
    ccom
    #
    chio
    @13
    ccom
    #
    chod
    co
    #
    @14
    @8
    @52
    @94
    @107
    wceq
    #
    @53
    chio
    clo
    wcel
    #
    @61
    @52
    @108
    @22
    @109
    idhmop
    chio
    hmoplin
    ax-mp
    @62
    chio
    chio
    @13
    hoddi
    mp3an12
    syl
    @8
    @105
    chio
    @106
    @13
    chod
    @105
    chio
    wceq
    @8
    chio
    @62
    hoid1i
    a1i
    @8
    @52
    @106
    @13
    wceq
    @53
    @13
    hoico2
    syl
    oveq12d
    eqtrd
    @8
    @95
    @13
    chio
    ccom
    #
    @31
    chod
    co
    #
    @103
    @8
    @13
    clo
    wcel
    #
    @52
    @95
    @111
    wceq
    #
    @8
    @23
    @112
    @25
    @13
    hmoplin
    syl
    @53
    @112
    @61
    @52
    @113
    @62
    @13
    chio
    @13
    hoddi
    mp3an2
    syl2anc
    @8
    @110
    @13
    @31
    chod
    @8
    @52
    @110
    @13
    wceq
    @53
    @13
    hoico1
    syl
    oveq1d
    eqtrd
    oveq12d
    @8
    @61
    @52
    wa
    @52
    @56
    @104
    @101
    wceq
    @8
    @52
    @61
    @53
    @62
    jctil
    @53
    @58
    chio
    @13
    @13
    @31
    hosubadd4
    syl12anc
    eqtrd
    @8
    @32
    @100
    @99
    chod
    @8
    @52
    @32
    @100
    wceq
    @53
    @13
    ho2times
    syl
    oveq2d
    @8
    @56
    @48
    @102
    @34
    wceq
    #
    @58
    @54
    @61
    @56
    @48
    @114
    @62
    chio
    @31
    @32
    hoaddsubass
    mp3an1
    syl2anc
    3eqtr2d
    eqtrd
    oveq1d
    @8
    @9
    @40
    c2
    chot
    @8
    @5
    @39
    chio
    chod
    vx
    vy
    cS
    cT
    cF
    @3
    opsqrlem2.1
    opsqrlem2.2
    opsqrlem2.3
    opsqrlem5
    oveq2d
    oveq2d
    3eqtr4d
    breqtrd
    @8
    @9
    cho
    wcel
    #
    @10
    @12
    wb
    #
    @8
    @22
    @5
    cho
    wcel
    #
    @115
    idhmop
    @8
    @4
    cn
    wcel
    @117
    @3
    peano2nn
    cn
    cho
    @4
    cF
    @24
    ffvelrni
    syl
    #
    chio
    @5
    hmopd
    sylancr
    c2
    cr
    wcel
    @115
    cc0
    c2
    clt
    wbr
    @116
    2re
    2pos
    c2
    @9
    leopmul
    mp3an13
    syl
    mpbird
    @8
    @117
    @22
    @6
    @10
    wb
    @118
    idhmop
    @5
    chio
    leop3
    sylancl
    mpbird
    nn1suc
end
