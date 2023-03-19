include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "c2.mm"
include "c3.mm"
include "cv.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "c9.mm"
include "cexp.mm"
include "cdiv.mm"
include "csu.mm"
include "cr.mm"
include "wcel.mm"
include "wtru.mm"
include "fzfid.mm"
include "wa.mm"
include "cn0.mm"
include "elfznn0.mm"
include "adantl.mm"
include "cn.mm"
include "2re.mm"
include "3nn.mm"
include "2nn0.mm"
include "nn0mulcl.mm"
include "mpan.mm"
include "nn0p1nn.mm"
include "syl.mm"
include "nnmulcl.mm"
include "sylancr.mm"
include "9nn.mm"
include "nnexpcl.mm"
include "nnmulcld.mm"
include "nndivre.mm"
include "fsumrecl.mm"
include "trud.mm"
include "nn0mulcli.mm"
include "ax-mp.mm"
include "nnmulcli.mm"
include "mp2an.mm"
include "cmin.mm"
include "wceq.mm"
include "cuz.mm"
include "cfv.mm"
include "nn0uz.mm"
include "eleqtri.mm"
include "a1i.mm"
include "cc.mm"
include "recnd.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "fsumm1.mm"
include "oveq2i.mm"
include "sumeq1i.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "2cn.mm"
include "nn0cni.mm"
include "adddii.mm"
include "eqtr3i.mm"
include "c7.mm"
include "c5.mm"
include "cle.mm"
include "7nn.mm"
include "nnnn0i.mm"
include "5nn.mm"
include "nnrei.mm"
include "remulcli.mm"
include "leidi.mm"
include "nncni.mm"
include "mulcomi.mm"
include "addcomi.mm"
include "expadd.mm"
include "mp3an.mm"
include "mul12i.mm"
include "3eqtri.mm"
include "c6.mm"
include "df-7.mm"
include "3cn.mm"
include "6nn0.mm"
include "expp1.mm"
include "expmul.mm"
include "3t2e6.mm"
include "sq3.mm"
include "3eqtr3i.mm"
include "mulassi.mm"
include "mul32i.mm"
include "mulcli.mm"
include "3eqtr4i.mm"
include "breqtri.mm"
include "log2ublem1.mm"

theorem log2ublem2
  let cB: class B
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cK: class K
  let cM: class M
  let cN: class N
  assume log2ublem2.1: |- ( ( ( 3 ^ 7 ) x. ( 5 x. 7 ) ) x. sum_ n e. ( 0 ... K ) ( 2 / ( ( 3 x. ( ( 2 x. n ) + 1 ) ) x. ( 9 ^ n ) ) ) ) <_ ( 2 x. B )
  assume log2ublem2.2: |- B e. NN0
  assume log2ublem2.3: |- F e. NN0
  assume log2ublem2.4: |- N e. NN0
  assume log2ublem2.5: |- ( N - 1 ) = K
  assume log2ublem2.6: |- ( B + F ) = G
  assume log2ublem2.7: |- M e. NN0
  assume log2ublem2.8: |- ( M + N ) = 3
  assume log2ublem2.9: |- ( ( 5 x. 7 ) x. ( 9 ^ M ) ) = ( ( ( 2 x. N ) + 1 ) x. F )

  disjoint K n
  disjoint N n
  assert |- ( ( ( 3 ^ 7 ) x. ( 5 x. 7 ) ) x. sum_ n e. ( 0 ... N ) ( 2 / ( ( 3 x. ( ( 2 x. n ) + 1 ) ) x. ( 9 ^ n ) ) ) ) <_ ( 2 x. G )

  proof
    cc0
    cK
    cfz
    co
    #
    c2
    c3
    c2
    vn
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    cmul
    co
    #
    c9
    @1
    cexp
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    vn
    csu
    #
    c2
    cB
    cmul
    co
    #
    cc0
    cN
    cfz
    co
    #
    @7
    vn
    csu
    #
    c2
    c3
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    cmul
    co
    #
    c9
    cN
    cexp
    co
    #
    cmul
    co
    #
    c2
    cF
    cmul
    co
    #
    c2
    cG
    cmul
    co
    #
    log2ublem2.1
    @8
    cr
    wcel
    wtru
    @0
    @7
    vn
    wtru
    cc0
    cK
    fzfid
    wtru
    @1
    @0
    wcel
    #
    wa
    @1
    cn0
    wcel
    #
    @7
    cr
    wcel
    #
    @19
    @20
    wtru
    @1
    cK
    elfznn0
    adantl
    @20
    c2
    cr
    wcel
    @6
    cn
    wcel
    @21
    2re
    @20
    @4
    @5
    @20
    c3
    cn
    wcel
    #
    @3
    cn
    wcel
    #
    @4
    cn
    wcel
    3nn
    @20
    @2
    cn0
    wcel
    #
    @23
    c2
    cn0
    wcel
    #
    @20
    @24
    2nn0
    c2
    @1
    nn0mulcl
    mpan
    @2
    nn0p1nn
    syl
    c3
    @3
    nnmulcl
    sylancr
    c9
    cn
    wcel
    #
    @20
    @5
    cn
    wcel
    9nn
    c9
    @1
    nnexpcl
    mpan
    nnmulcld
    c2
    @6
    nndivre
    sylancr
    #
    syl
    fsumrecl
    trud
    2nn0
    @14
    @15
    c3
    @13
    3nn
    @12
    cn0
    wcel
    @13
    cn
    wcel
    c2
    cN
    2nn0
    log2ublem2.4
    nn0mulcli
    @12
    nn0p1nn
    ax-mp
    #
    nnmulcli
    @26
    cN
    cn0
    wcel
    #
    @15
    cn
    wcel
    9nn
    log2ublem2.4
    c9
    cN
    nnexpcl
    mp2an
    #
    nnmulcli
    #
    c2
    cB
    2nn0
    log2ublem2.2
    nn0mulcli
    c2
    cF
    2nn0
    log2ublem2.3
    nn0mulcli
    @11
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    @7
    vn
    csu
    #
    c2
    @16
    cdiv
    co
    #
    caddc
    co
    #
    @8
    @35
    caddc
    co
    @11
    @36
    wceq
    wtru
    @7
    @35
    vn
    cc0
    cN
    cN
    cc0
    cuz
    cfv
    #
    wcel
    wtru
    cN
    cn0
    @37
    log2ublem2.4
    nn0uz
    eleqtri
    a1i
    wtru
    @1
    @10
    wcel
    #
    wa
    @20
    @7
    cc
    wcel
    @38
    @20
    wtru
    @1
    cN
    elfznn0
    adantl
    @20
    @7
    @27
    recnd
    syl
    @1
    cN
    wceq
    #
    @6
    @16
    c2
    cdiv
    @39
    @4
    @14
    @5
    @15
    cmul
    @39
    @3
    @13
    c3
    cmul
    @39
    @2
    @12
    c1
    caddc
    @1
    cN
    c2
    cmul
    oveq2
    oveq1d
    oveq2d
    @1
    cN
    c9
    cexp
    oveq2
    oveq12d
    oveq2d
    fsumm1
    trud
    @34
    @8
    @35
    caddc
    @33
    @0
    @7
    vn
    @32
    cK
    cc0
    cfz
    log2ublem2.5
    oveq2i
    sumeq1i
    oveq1i
    eqtri
    c2
    cB
    cF
    caddc
    co
    #
    cmul
    co
    @9
    @17
    caddc
    co
    @18
    c2
    cB
    cF
    2cn
    cB
    log2ublem2.2
    nn0cni
    cF
    log2ublem2.3
    nn0cni
    #
    adddii
    @40
    cG
    c2
    cmul
    log2ublem2.6
    oveq2i
    eqtr3i
    c3
    c7
    cexp
    co
    #
    c5
    c7
    cmul
    co
    #
    cmul
    co
    #
    c2
    cmul
    co
    #
    @45
    @16
    @17
    cmul
    co
    #
    cle
    @45
    @44
    c2
    @44
    @42
    @43
    @22
    c7
    cn0
    wcel
    @42
    cn
    wcel
    3nn
    c7
    7nn
    nnnn0i
    c3
    c7
    nnexpcl
    mp2an
    #
    c5
    c7
    5nn
    7nn
    nnmulcli
    #
    nnmulcli
    nnrei
    2re
    remulcli
    leidi
    c2
    @44
    cmul
    co
    c2
    @16
    cF
    cmul
    co
    #
    cmul
    co
    @45
    @46
    @44
    @49
    c2
    cmul
    c3
    c9
    c3
    cexp
    co
    #
    @43
    cmul
    co
    #
    cmul
    co
    #
    c3
    @15
    @13
    cF
    cmul
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    @44
    @49
    @51
    @54
    c3
    cmul
    @51
    @15
    @43
    c9
    cM
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    @54
    @51
    @43
    @50
    cmul
    co
    @43
    @15
    @56
    cmul
    co
    #
    cmul
    co
    @58
    @50
    @43
    @50
    @26
    c3
    cn0
    wcel
    #
    @50
    cn
    wcel
    9nn
    c3
    3nn
    nnnn0i
    #
    c9
    c3
    nnexpcl
    mp2an
    nncni
    #
    @43
    @48
    nncni
    #
    mulcomi
    @50
    @59
    @43
    cmul
    @50
    c9
    cN
    cM
    caddc
    co
    #
    cexp
    co
    #
    @59
    c3
    @64
    c9
    cexp
    cM
    cN
    caddc
    co
    c3
    @64
    log2ublem2.8
    cM
    cN
    cM
    log2ublem2.7
    nn0cni
    cN
    log2ublem2.4
    nn0cni
    addcomi
    eqtr3i
    oveq2i
    c9
    cc
    wcel
    @29
    cM
    cn0
    wcel
    #
    @65
    @59
    wceq
    c9
    9nn
    nncni
    log2ublem2.4
    log2ublem2.7
    c9
    cN
    cM
    expadd
    mp3an
    eqtri
    oveq2i
    @43
    @15
    @56
    @63
    @15
    @30
    nncni
    #
    @56
    @26
    @66
    @56
    cn
    wcel
    9nn
    log2ublem2.7
    c9
    cM
    nnexpcl
    mp2an
    nncni
    mul12i
    3eqtri
    @57
    @53
    @15
    cmul
    log2ublem2.9
    oveq2i
    eqtri
    oveq2i
    @44
    c3
    @50
    cmul
    co
    #
    @43
    cmul
    co
    @52
    @42
    @68
    @43
    cmul
    @42
    c3
    c6
    c1
    caddc
    co
    #
    cexp
    co
    #
    @50
    c3
    cmul
    co
    #
    @68
    c7
    @69
    c3
    cexp
    df-7
    oveq2i
    @70
    c3
    c6
    cexp
    co
    #
    c3
    cmul
    co
    #
    @71
    c3
    cc
    wcel
    #
    c6
    cn0
    wcel
    @70
    @73
    wceq
    3cn
    6nn0
    c3
    c6
    expp1
    mp2an
    @72
    @50
    c3
    cmul
    c3
    c2
    c3
    cmul
    co
    #
    cexp
    co
    #
    c3
    c2
    cexp
    co
    #
    c3
    cexp
    co
    #
    @72
    @50
    @74
    @25
    @60
    @76
    @78
    wceq
    3cn
    2nn0
    @61
    c3
    c2
    c3
    expmul
    mp3an
    @75
    c6
    c3
    cexp
    @75
    c3
    c2
    cmul
    co
    c6
    c2
    c3
    2cn
    3cn
    mulcomi
    3t2e6
    eqtri
    oveq2i
    @77
    c9
    c3
    cexp
    sq3
    oveq1i
    3eqtr3i
    oveq1i
    eqtri
    @50
    c3
    @62
    3cn
    mulcomi
    3eqtri
    oveq1i
    c3
    @50
    @43
    3cn
    @62
    @63
    mulassi
    eqtri
    @49
    c3
    @15
    cmul
    co
    #
    @13
    cmul
    co
    #
    cF
    cmul
    co
    @79
    @53
    cmul
    co
    @55
    @16
    @80
    cF
    cmul
    c3
    @13
    @15
    3cn
    @13
    @28
    nncni
    #
    @67
    mul32i
    oveq1i
    @79
    @13
    cF
    c3
    @15
    3cn
    @67
    mulcli
    @81
    @41
    mulassi
    c3
    @15
    @53
    3cn
    @67
    @13
    cF
    @81
    @41
    mulcli
    mulassi
    3eqtri
    3eqtr4i
    oveq2i
    @44
    c2
    @42
    @43
    @42
    @47
    nncni
    @63
    mulcli
    2cn
    mulcomi
    @16
    c2
    cF
    @16
    @31
    nncni
    2cn
    @41
    mul12i
    3eqtr4i
    breqtri
    log2ublem1
end
