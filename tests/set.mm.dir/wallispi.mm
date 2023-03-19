include "c1.mm"
include "c2.mm"
include "cpi.mm"
include "cdiv.mm"
include "co.mm"
include "cli.mm"
include "wbr.mm"
include "wtru.mm"
include "cn.mm"
include "cv.mm"
include "cmul.mm"
include "cseq.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cn0.mm"
include "cc0.mm"
include "cioo.mm"
include "csin.mm"
include "cexp.mm"
include "citg.mm"
include "caddc.mm"
include "eqid.mm"
include "wallispilem5.mm"
include "a1i.mm"
include "2cnd.mm"
include "cc.mm"
include "wcel.mm"
include "picn.mm"
include "wne.mm"
include "pire.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "divcld.mm"
include "nnex.mm"
include "mptex.mm"
include "wf.mm"
include "halfcld.mm"
include "crp.mm"
include "cuz.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "cfz.mm"
include "cmin.mm"
include "wceq.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "adantl.mm"
include "elfznn.mm"
include "nncn.mm"
include "mulcld.mm"
include "1cnd.mm"
include "subcld.mm"
include "1red.mm"
include "clt.mm"
include "1t1e1.mm"
include "remulcld.mm"
include "cr.mm"
include "2re.mm"
include "nnre.mm"
include "1rp.mm"
include "1lt2.mm"
include "ltmul1dd.mm"
include "cle.mm"
include "0le2.mm"
include "nnge1.mm"
include "lemul2ad.mm"
include "ltletrd.mm"
include "syl5eqbrr.mm"
include "gtned.mm"
include "subne0d.mm"
include "addcld.mm"
include "0red.mm"
include "readdcld.mm"
include "rpgt0d.mm"
include "2rp.mm"
include "nnrp.mm"
include "rpmulcld.mm"
include "ltaddrp2d.mm"
include "lttrd.mm"
include "syl.mm"
include "fvmptd.mm"
include "nnrpd.mm"
include "resubcld.mm"
include "1m1e0.mm"
include "ltsub1dd.mm"
include "elrpd.mm"
include "rpdivcld.mm"
include "nnred.mm"
include "rpge0d.mm"
include "mulge0d.mm"
include "ge0p1rpd.mm"
include "eqeltrd.mm"
include "wa.mm"
include "rpmulcl.mm"
include "seqcl.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "reccld.mm"
include "fmpti.mm"
include "ffvelrnda.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "vtoclga.mm"
include "divrecd.mm"
include "divcan6d.mm"
include "eqcomd.mm"
include "mulassd.mm"
include "3eqtrd.mm"
include "eqidd.mm"
include "oveq2d.mm"
include "id.mm"
include "rpreccld.mm"
include "3eqtr4d.mm"
include "climmulc2.mm"
include "2cn.mm"
include "divcli.mm"
include "mulid1i.mm"
include "syl6breq.mm"
include "2ne0.mm"
include "divne0i.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "recne0d.mm"
include "eqnetrd.mm"
include "nelsn.mm"
include "eldifd.mm"
include "recrecd.mm"
include "fvmpt3.mm"
include "3eqtr4rd.mm"
include "eqeltri.mm"
include "climrec.mm"
include "trud.mm"
include "recdiv.mm"
include "mp4an.mm"
include "breqtri.mm"

theorem wallispi
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cW: class W
  let vj: setvar j
  let vw: setvar w
  let vx: setvar x
  assume wallispi.1: |- F = ( k e. NN |-> ( ( ( 2 x. k ) / ( ( 2 x. k ) - 1 ) ) x. ( ( 2 x. k ) / ( ( 2 x. k ) + 1 ) ) ) )
  assume wallispi.2: |- W = ( n e. NN |-> ( seq 1 ( x. , F ) ` n ) )

  disjoint k n
  disjoint F n
  disjoint j k
  disjoint j n
  disjoint j w
  disjoint n w
  disjoint k x
  disjoint n x
  disjoint F j
  disjoint F w
  disjoint F x
  disjoint W j
  disjoint k x
  assert |- W ~~> ( _pi / 2 )

  proof
    cW
    c1
    c2
    cpi
    cdiv
    co
    #
    cdiv
    co
    #
    cpi
    c2
    cdiv
    co
    #
    cli
    cW
    @1
    cli
    wbr
    wtru
    @0
    vj
    vn
    cn
    c1
    vn
    cv
    #
    cmul
    cF
    c1
    cseq
    #
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    cW
    c1
    cvv
    cn
    nnuz
    wtru
    1zzd
    #
    wtru
    @7
    @0
    c1
    cmul
    co
    @0
    cli
    wtru
    c1
    @0
    vj
    vn
    cn
    @2
    @6
    cmul
    co
    #
    cmpt
    #
    @7
    c1
    cvv
    cn
    nnuz
    @8
    @10
    c1
    cli
    wbr
    wtru
    vx
    vk
    vn
    cF
    vn
    cn
    c2
    @3
    cmul
    co
    #
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
    @3
    cexp
    co
    citg
    cmpt
    #
    cfv
    @11
    c1
    caddc
    co
    #
    @12
    cfv
    cdiv
    co
    cmpt
    #
    @10
    @12
    vn
    cn
    @13
    @11
    cdiv
    co
    cmpt
    #
    wallispi.1
    @12
    eqid
    @14
    eqid
    @10
    eqid
    #
    @15
    eqid
    wallispilem5
    a1i
    wtru
    c2
    cpi
    wtru
    2cnd
    cpi
    cc
    wcel
    #
    wtru
    picn
    a1i
    cpi
    cc0
    wne
    #
    wtru
    cpi
    pire
    pipos
    gt0ne0ii
    #
    a1i
    divcld
    @7
    cvv
    wcel
    wtru
    vn
    cn
    @6
    nnex
    mptex
    a1i
    wtru
    cn
    cc
    vj
    cv
    #
    @10
    cn
    cc
    @10
    wf
    wtru
    vn
    cn
    cc
    @9
    @10
    @16
    @3
    cn
    wcel
    #
    @2
    @6
    @21
    cpi
    @17
    @21
    picn
    a1i
    halfcld
    @21
    @5
    @21
    @5
    @21
    vj
    vw
    cmul
    crp
    cF
    c1
    @3
    @21
    @3
    c1
    cuz
    cfv
    wcel
    @3
    elnnuz
    biimpi
    @20
    c1
    @3
    cfz
    co
    wcel
    #
    @20
    cF
    cfv
    #
    crp
    wcel
    @21
    @22
    @23
    c2
    @20
    cmul
    co
    #
    @24
    c1
    cmin
    co
    #
    cdiv
    co
    #
    @24
    @24
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    crp
    @22
    vk
    @20
    c2
    vk
    cv
    #
    cmul
    co
    #
    @31
    c1
    cmin
    co
    #
    cdiv
    co
    #
    @31
    @31
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @29
    cn
    cF
    cc
    cF
    vk
    cn
    @36
    cmpt
    wceq
    @22
    wallispi.1
    a1i
    vk
    vj
    weq
    #
    @36
    @29
    wceq
    @22
    @37
    @33
    @26
    @35
    @28
    cmul
    @37
    @31
    @24
    @32
    @25
    cdiv
    @30
    @20
    c2
    cmul
    oveq2
    #
    @37
    @31
    @24
    c1
    cmin
    @38
    oveq1d
    oveq12d
    @37
    @31
    @24
    @34
    @27
    cdiv
    @38
    @37
    @31
    @24
    c1
    caddc
    @38
    oveq1d
    oveq12d
    oveq12d
    adantl
    @20
    @3
    elfznn
    #
    @22
    @20
    cn
    wcel
    #
    @29
    cc
    wcel
    @39
    @40
    @26
    @28
    @40
    @24
    @25
    @40
    c2
    @20
    @40
    2cnd
    #
    @20
    nncn
    mulcld
    #
    @40
    @24
    c1
    @42
    @40
    1cnd
    #
    subcld
    @40
    @24
    c1
    @42
    @43
    @40
    c1
    @24
    @40
    1red
    #
    @40
    c1
    c1
    c1
    cmul
    co
    #
    @24
    clt
    1t1e1
    @40
    @45
    c2
    c1
    cmul
    co
    @24
    @40
    c1
    c1
    @44
    @44
    remulcld
    @40
    c2
    c1
    c2
    cr
    wcel
    #
    @40
    2re
    a1i
    #
    @44
    remulcld
    @40
    c2
    @20
    @47
    @20
    nnre
    #
    remulcld
    #
    @40
    c1
    c2
    c1
    @44
    @47
    c1
    crp
    wcel
    @40
    1rp
    a1i
    #
    c1
    c2
    clt
    wbr
    @40
    1lt2
    a1i
    ltmul1dd
    @40
    c1
    @20
    c2
    @44
    @48
    @47
    cc0
    c2
    cle
    wbr
    @40
    0le2
    a1i
    @20
    nnge1
    lemul2ad
    ltletrd
    syl5eqbrr
    #
    gtned
    subne0d
    divcld
    @40
    @24
    @27
    @42
    @40
    @24
    c1
    @42
    @43
    addcld
    @40
    cc0
    @27
    @40
    0red
    #
    @40
    cc0
    c1
    @27
    @52
    @44
    @40
    @24
    c1
    @49
    @44
    readdcld
    @40
    c1
    @50
    rpgt0d
    @40
    c1
    @24
    @44
    @40
    c2
    @20
    c2
    crp
    wcel
    #
    @40
    2rp
    a1i
    #
    @20
    nnrp
    rpmulcld
    ltaddrp2d
    lttrd
    gtned
    divcld
    mulcld
    syl
    fvmptd
    @22
    @26
    @28
    @22
    @24
    @25
    @22
    c2
    @20
    @53
    @22
    2rp
    a1i
    #
    @22
    @20
    @39
    nnrpd
    #
    rpmulcld
    #
    @22
    @40
    @25
    crp
    wcel
    @39
    @40
    @25
    @40
    @24
    c1
    @49
    @44
    resubcld
    @40
    cc0
    c1
    c1
    cmin
    co
    @25
    clt
    1m1e0
    @40
    c1
    @24
    c1
    @44
    @49
    @44
    @51
    ltsub1dd
    syl5eqbrr
    elrpd
    syl
    rpdivcld
    @22
    @24
    @27
    @57
    @22
    @24
    @22
    c2
    @20
    @46
    @22
    2re
    a1i
    #
    @22
    @20
    @39
    nnred
    #
    remulcld
    @22
    c2
    @20
    @58
    @59
    @22
    c2
    @55
    rpge0d
    @22
    @20
    @56
    rpge0d
    mulge0d
    ge0p1rpd
    rpdivcld
    rpmulcld
    eqeltrd
    adantl
    @20
    crp
    wcel
    vw
    cv
    #
    crp
    wcel
    wa
    @20
    @60
    cmul
    co
    crp
    wcel
    @21
    @20
    @60
    rpmulcl
    adantl
    seqcl
    #
    rpcnd
    @21
    @5
    @61
    rpne0d
    reccld
    mulcld
    fmpti
    a1i
    ffvelrnda
    @40
    @20
    @7
    cfv
    #
    @0
    @20
    @10
    cfv
    #
    cmul
    co
    #
    wceq
    wtru
    @40
    c1
    @20
    @4
    cfv
    #
    cdiv
    co
    #
    @0
    @2
    @66
    cmul
    co
    #
    cmul
    co
    #
    @62
    @64
    @40
    @66
    c1
    @66
    cmul
    co
    @0
    @2
    cmul
    co
    #
    @66
    cmul
    co
    @68
    @40
    c1
    @65
    @43
    @40
    @65
    @5
    crp
    wcel
    @65
    crp
    wcel
    vn
    @20
    cn
    vn
    vj
    weq
    #
    @5
    @65
    crp
    @3
    @20
    @4
    fveq2
    #
    eleq1d
    @61
    vtoclga
    #
    rpcnd
    #
    @40
    @65
    @72
    rpne0d
    #
    divrecd
    @40
    c1
    @69
    @66
    cmul
    @40
    @69
    c1
    @40
    c2
    cpi
    @41
    @17
    @40
    picn
    a1i
    #
    @40
    c2
    @54
    rpne0d
    @18
    @40
    @19
    a1i
    #
    divcan6d
    eqcomd
    oveq1d
    @40
    @0
    @2
    @66
    @40
    c2
    cpi
    @41
    @75
    @76
    divcld
    @40
    cpi
    @75
    halfcld
    #
    @40
    @65
    @73
    @74
    reccld
    #
    mulassd
    3eqtrd
    @40
    vn
    @20
    @6
    @66
    cn
    @7
    crp
    @40
    @7
    eqidd
    #
    @70
    @6
    @66
    wceq
    @40
    @70
    @5
    @65
    c1
    cdiv
    @71
    oveq2d
    adantl
    #
    @40
    id
    #
    @40
    @65
    @72
    rpreccld
    fvmptd
    #
    @40
    @63
    @67
    @0
    cmul
    @40
    vn
    @20
    @9
    @67
    cn
    @10
    cc
    @40
    @10
    eqidd
    @40
    @70
    wa
    @6
    @66
    @2
    cmul
    @80
    oveq2d
    @81
    @40
    @2
    @66
    @77
    @78
    mulcld
    fvmptd
    oveq2d
    3eqtr4d
    adantl
    climmulc2
    @0
    c2
    cpi
    2cn
    picn
    @19
    divcli
    mulid1i
    syl6breq
    @0
    cc0
    wne
    wtru
    c2
    cpi
    2cn
    picn
    2ne0
    @19
    divne0i
    a1i
    @40
    @62
    cc
    cc0
    csn
    #
    cdif
    wcel
    wtru
    @40
    @62
    cc
    @83
    @40
    @62
    @66
    cc
    @82
    @78
    eqeltrd
    @40
    @62
    cc0
    wne
    @62
    @83
    wcel
    wn
    @40
    @62
    @66
    cc0
    @82
    @40
    @65
    @73
    @74
    recne0d
    eqnetrd
    @62
    cc0
    nelsn
    syl
    eldifd
    adantl
    @40
    @20
    cW
    cfv
    #
    c1
    @62
    cdiv
    co
    #
    wceq
    wtru
    @40
    c1
    @66
    cdiv
    co
    @65
    @85
    @84
    @40
    @65
    @73
    @74
    recrecd
    @40
    @62
    @66
    c1
    cdiv
    @40
    vn
    @20
    @6
    @66
    cn
    @7
    cc
    @79
    @80
    @81
    @78
    fvmptd
    oveq2d
    vn
    @20
    @5
    @65
    cn
    cW
    crp
    @71
    wallispi.2
    @61
    fvmpt3
    3eqtr4rd
    adantl
    cW
    cvv
    wcel
    wtru
    cW
    vn
    cn
    @5
    cmpt
    cvv
    wallispi.2
    vn
    cn
    @5
    nnex
    mptex
    eqeltri
    a1i
    climrec
    trud
    c2
    cc
    wcel
    c2
    cc0
    wne
    @17
    @18
    @1
    @2
    wceq
    2cn
    2ne0
    picn
    @19
    c2
    cpi
    recdiv
    mp4an
    breqtri
end
