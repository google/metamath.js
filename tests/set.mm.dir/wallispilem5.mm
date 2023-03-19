include "c1.mm"
include "cli.mm"
include "wallispilem4.mm"
include "wbr.mm"
include "wtru.mm"
include "cvv.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "c2.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "1cnd.mm"
include "clim1fr1.mm"
include "wcel.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cfv.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmpt.mm"
include "nnex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "cr.mm"
include "wf.mm"
include "cn0.mm"
include "2nn0.mm"
include "nnnn0.mm"
include "nn0mulcld.mm"
include "1nn0.mm"
include "nn0addcld.mm"
include "nn0red.mm"
include "nncn.mm"
include "nnne0.mm"
include "mulne0d.mm"
include "redivcld.mm"
include "fmpti.mm"
include "ffvelrnda.mm"
include "crp.mm"
include "wallispilem3.mm"
include "syl.mm"
include "rpred.mm"
include "rerpdivcld.mm"
include "cle.mm"
include "cmin.mm"
include "2nn.mm"
include "id.mm"
include "nnmulcld.mm"
include "nnm1nn0.mm"
include "mulcld.mm"
include "npcand.mm"
include "fveq2d.mm"
include "wallispilem1.mm"
include "eqbrtrrd.mm"
include "lediv1dd.mm"
include "addcld.mm"
include "divcld.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divcan4d.mm"
include "cuz.mm"
include "2re.mm"
include "nnre.mm"
include "remulcld.mm"
include "1red.mm"
include "readdcld.mm"
include "nn0ge0d.mm"
include "nnge1.mm"
include "lemulge11d.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "ltled.mm"
include "cz.mm"
include "wb.mm"
include "nn0zd.mm"
include "eluz.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "itgsinexp.mm"
include "pncand.mm"
include "oveq1d.mm"
include "wceq.mm"
include "1e2m1.mm"
include "oveq2d.mm"
include "subsub3d.mm"
include "eqtr2d.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "peano2nnd.mm"
include "nnne0d.mm"
include "mulassd.mm"
include "divcan6d.mm"
include "mulid2d.mm"
include "3eqtr2d.mm"
include "eqtr3d.mm"
include "breqtrrd.mm"
include "rpdivcld.mm"
include "nfcv.mm"
include "cpi.mm"
include "cioo.mm"
include "csin.mm"
include "cexp.mm"
include "citg.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfov.mm"
include "oveq2.mm"
include "fvmptf.mm"
include "mpdan.mm"
include "cc.mm"
include "wa.mm"
include "simpr.mm"
include "fvmptd.mm"
include "3brtr4d.mm"
include "adantl.mm"
include "dividd.mm"
include "climsqz2.mm"
include "trud.mm"
include "eqbrtrri.mm"

theorem wallispilem5
  let vx: setvar x
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cL: class L
  assume wallispilem5.1: |- F = ( k e. NN |-> ( ( ( 2 x. k ) / ( ( 2 x. k ) - 1 ) ) x. ( ( 2 x. k ) / ( ( 2 x. k ) + 1 ) ) ) )
  assume wallispilem5.2: |- I = ( n e. NN0 |-> S. ( 0 (,) _pi ) ( ( sin ` x ) ^ n ) _d x )
  assume wallispilem5.3: |- G = ( n e. NN |-> ( ( I ` ( 2 x. n ) ) / ( I ` ( ( 2 x. n ) + 1 ) ) ) )
  assume wallispilem5.4: |- H = ( n e. NN |-> ( ( _pi / 2 ) x. ( 1 / ( seq 1 ( x. , F ) ` n ) ) ) )
  assume wallispilem5.5: |- L = ( n e. NN |-> ( ( ( 2 x. n ) + 1 ) / ( 2 x. n ) ) )

  disjoint k n
  disjoint k x
  disjoint n x
  disjoint F x
  disjoint G k
  disjoint L k
  disjoint k x
  assert |- H ~~> 1

  proof
    cG
    cH
    c1
    cli
    vx
    vk
    vn
    cF
    cG
    cH
    cI
    wallispilem5.1
    wallispilem5.2
    wallispilem5.3
    wallispilem5.4
    wallispilem4
    cG
    c1
    cli
    wbr
    wtru
    c1
    vk
    cL
    cG
    c1
    cvv
    cn
    nnuz
    wtru
    1zzd
    wtru
    c2
    c1
    vn
    cL
    wallispilem5.5
    wtru
    2cnd
    c2
    cc0
    wne
    #
    wtru
    2ne0
    a1i
    wtru
    1cnd
    clim1fr1
    cG
    cvv
    wcel
    wtru
    cG
    vn
    cn
    c2
    vn
    cv
    #
    cmul
    co
    #
    cI
    cfv
    #
    @2
    c1
    caddc
    co
    #
    cI
    cfv
    #
    cdiv
    co
    #
    cmpt
    cvv
    wallispilem5.3
    vn
    cn
    @6
    nnex
    mptex
    eqeltri
    a1i
    wtru
    cn
    cr
    vk
    cv
    #
    cL
    cn
    cr
    cL
    wf
    wtru
    vn
    cn
    cr
    @4
    @2
    cdiv
    co
    #
    cL
    wallispilem5.5
    @1
    cn
    wcel
    #
    @4
    @2
    @9
    @4
    @9
    @2
    c1
    @9
    c2
    @1
    c2
    cn0
    wcel
    #
    @9
    2nn0
    a1i
    @1
    nnnn0
    nn0mulcld
    #
    c1
    cn0
    wcel
    #
    @9
    1nn0
    a1i
    nn0addcld
    #
    nn0red
    @9
    @2
    @11
    nn0red
    @9
    c2
    @1
    @9
    2cnd
    @1
    nncn
    @0
    @9
    2ne0
    a1i
    @1
    nnne0
    mulne0d
    redivcld
    fmpti
    a1i
    ffvelrnda
    wtru
    cn
    cr
    @7
    cG
    cn
    cr
    cG
    wf
    wtru
    vn
    cn
    cr
    @6
    cG
    wallispilem5.3
    @9
    @3
    @5
    @9
    @3
    @9
    @2
    cn0
    wcel
    @3
    crp
    wcel
    @11
    vx
    vn
    cI
    @2
    wallispilem5.2
    wallispilem3
    syl
    rpred
    @9
    @4
    cn0
    wcel
    @5
    crp
    wcel
    @13
    vx
    vn
    cI
    @4
    wallispilem5.2
    wallispilem3
    syl
    rerpdivcld
    fmpti
    a1i
    ffvelrnda
    @7
    cn
    wcel
    #
    @7
    cG
    cfv
    #
    @7
    cL
    cfv
    #
    cle
    wbr
    wtru
    @14
    c2
    @7
    cmul
    co
    #
    cI
    cfv
    #
    @17
    c1
    caddc
    co
    #
    cI
    cfv
    #
    cdiv
    co
    #
    @19
    @17
    cdiv
    co
    #
    @15
    @16
    cle
    @14
    @21
    @17
    c1
    cmin
    co
    #
    cI
    cfv
    #
    @20
    cdiv
    co
    #
    @22
    cle
    @14
    @18
    @24
    @20
    @14
    @18
    @14
    @17
    cn0
    wcel
    @18
    crp
    wcel
    @14
    c2
    @7
    @10
    @14
    2nn0
    a1i
    #
    @7
    nnnn0
    nn0mulcld
    #
    vx
    vn
    cI
    @17
    wallispilem5.2
    wallispilem3
    syl
    #
    rpred
    #
    @14
    @24
    @14
    @23
    cn0
    wcel
    #
    @24
    crp
    wcel
    @14
    @17
    cn
    wcel
    @30
    @14
    c2
    @7
    c2
    cn
    wcel
    @14
    2nn
    a1i
    @14
    id
    #
    nnmulcld
    #
    @17
    nnm1nn0
    syl
    #
    vx
    vn
    cI
    @23
    wallispilem5.2
    wallispilem3
    syl
    #
    rpred
    @14
    @19
    cn0
    wcel
    @20
    crp
    wcel
    @14
    @17
    c1
    @27
    @12
    @14
    1nn0
    a1i
    nn0addcld
    #
    vx
    vn
    cI
    @19
    wallispilem5.2
    wallispilem3
    syl
    #
    @14
    @23
    c1
    caddc
    co
    #
    cI
    cfv
    @18
    @24
    cle
    @14
    @37
    @17
    cI
    @14
    @17
    c1
    @14
    c2
    @7
    @14
    2cnd
    #
    @7
    nncn
    #
    mulcld
    #
    @14
    1cnd
    #
    npcand
    fveq2d
    @14
    vx
    vn
    cI
    @23
    wallispilem5.2
    @33
    wallispilem1
    eqbrtrrd
    lediv1dd
    @14
    @22
    @20
    cmul
    co
    #
    @20
    cdiv
    co
    @22
    @25
    @14
    @22
    @20
    @14
    @19
    @17
    @14
    @17
    c1
    @40
    @41
    addcld
    #
    @40
    @14
    c2
    @7
    @38
    @39
    @0
    @14
    2ne0
    a1i
    @7
    nnne0
    mulne0d
    #
    divcld
    #
    @14
    @20
    @36
    rpcnd
    #
    @14
    @20
    @36
    rpne0d
    #
    divcan4d
    @14
    @42
    @24
    @20
    cdiv
    @14
    @42
    @22
    @17
    @19
    cdiv
    co
    #
    @24
    cmul
    co
    #
    cmul
    co
    @22
    @48
    cmul
    co
    #
    @24
    cmul
    co
    #
    @24
    @14
    @20
    @49
    @22
    cmul
    @14
    @20
    @19
    c1
    cmin
    co
    #
    @19
    cdiv
    co
    #
    @19
    c2
    cmin
    co
    #
    cI
    cfv
    #
    cmul
    co
    @49
    @14
    vx
    vn
    cI
    @19
    wallispilem5.2
    @14
    @19
    c2
    cuz
    cfv
    wcel
    #
    c2
    @19
    cle
    wbr
    #
    @14
    c2
    @19
    c2
    cr
    wcel
    @14
    2re
    a1i
    #
    @14
    @17
    c1
    @14
    c2
    @7
    @58
    @7
    nnre
    #
    remulcld
    #
    @14
    1red
    readdcld
    #
    @14
    c2
    @17
    @19
    @58
    @60
    @61
    @14
    c2
    @7
    @58
    @59
    @14
    c2
    @26
    nn0ge0d
    @7
    nnge1
    lemulge11d
    @14
    @17
    @60
    ltp1d
    lelttrd
    ltled
    @14
    c2
    cz
    wcel
    @19
    cz
    wcel
    @56
    @57
    wb
    @14
    c2
    @26
    nn0zd
    @14
    @19
    @35
    nn0zd
    c2
    @19
    eluz
    syl2anc
    mpbird
    itgsinexp
    @14
    @53
    @48
    @55
    @24
    cmul
    @14
    @52
    @17
    @19
    cdiv
    @14
    @17
    c1
    @40
    @41
    pncand
    oveq1d
    @14
    @54
    @23
    cI
    @14
    @23
    @17
    c2
    c1
    cmin
    co
    #
    cmin
    co
    @54
    @14
    c1
    @62
    @17
    cmin
    c1
    @62
    wceq
    @14
    1e2m1
    a1i
    oveq2d
    @14
    @17
    c2
    c1
    @40
    @38
    @41
    subsub3d
    eqtr2d
    fveq2d
    oveq12d
    eqtrd
    oveq2d
    @14
    @22
    @48
    @24
    @45
    @14
    @17
    @19
    @40
    @43
    @14
    @19
    @14
    @17
    @32
    peano2nnd
    nnne0d
    #
    divcld
    @14
    @24
    @34
    rpcnd
    #
    mulassd
    @14
    @51
    c1
    @24
    cmul
    co
    @24
    @14
    @50
    c1
    @24
    cmul
    @14
    @19
    @17
    @43
    @40
    @63
    @44
    divcan6d
    oveq1d
    @14
    @24
    @64
    mulid2d
    eqtrd
    3eqtr2d
    oveq1d
    eqtr3d
    breqtrrd
    @14
    @21
    crp
    wcel
    @15
    @21
    wceq
    @14
    @18
    @20
    @28
    @36
    rpdivcld
    vn
    @7
    @6
    @21
    cn
    cG
    crp
    vn
    @7
    nfcv
    vn
    @18
    @20
    cdiv
    vn
    @17
    cI
    vn
    cI
    vn
    cn0
    vx
    cc0
    cpi
    cioo
    co
    vx
    cv
    csin
    cfv
    @1
    cexp
    co
    citg
    #
    cmpt
    wallispilem5.2
    vn
    cn0
    @65
    nfmpt1
    nfcxfr
    #
    vn
    @17
    nfcv
    nffv
    vn
    cdiv
    nfcv
    vn
    @19
    cI
    @66
    vn
    @19
    nfcv
    nffv
    nfov
    @1
    @7
    wceq
    #
    @3
    @18
    @5
    @20
    cdiv
    @67
    @2
    @17
    cI
    @1
    @7
    c2
    cmul
    oveq2
    #
    fveq2d
    @67
    @4
    @19
    cI
    @67
    @2
    @17
    c1
    caddc
    @68
    oveq1d
    fveq2d
    oveq12d
    wallispilem5.3
    fvmptf
    mpdan
    #
    @14
    vn
    @7
    @8
    @22
    cn
    cL
    cc
    cL
    vn
    cn
    @8
    cmpt
    wceq
    @14
    wallispilem5.5
    a1i
    @14
    @67
    wa
    #
    @4
    @19
    @2
    @17
    cdiv
    @70
    @2
    @17
    c1
    caddc
    @70
    @1
    @7
    c2
    cmul
    @14
    @67
    simpr
    oveq2d
    #
    oveq1d
    @71
    oveq12d
    @31
    @45
    fvmptd
    3brtr4d
    adantl
    @14
    c1
    @15
    cle
    wbr
    wtru
    @14
    c1
    @21
    @15
    cle
    @14
    @20
    @20
    cdiv
    co
    c1
    @21
    cle
    @14
    @20
    @46
    @47
    dividd
    @14
    @20
    @18
    @20
    @14
    @20
    @36
    rpred
    @29
    @36
    @14
    vx
    vn
    cI
    @17
    wallispilem5.2
    @27
    wallispilem1
    lediv1dd
    eqbrtrrd
    @69
    breqtrrd
    adantl
    climsqz2
    trud
    eqbrtrri
end
