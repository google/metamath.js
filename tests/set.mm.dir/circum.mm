include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cli.mm"
include "wbr.mm"
include "wtru.mm"
include "cn.mm"
include "cv.mm"
include "cdiv.mm"
include "csin.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cr.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "ccom.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "crp.mm"
include "pirp.mm"
include "nnrp.mm"
include "rpdivcl.mm"
include "sylancr.mm"
include "rprene0d.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "adantl.mm"
include "eqidd.mm"
include "wceq.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "fmptco.mm"
include "wf.mm"
include "eqid.mm"
include "fmpti.mm"
include "cc.mm"
include "pire.mm"
include "recni.mm"
include "divcnv.mm"
include "mp1i.mm"
include "sinccvg.mm"
include "eqbrtrrd.mm"
include "2re.mm"
include "remulcli.mm"
include "a1i.mm"
include "nnex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "eldifi.mm"
include "resincld.mm"
include "eldifsni.mm"
include "redivcld.mm"
include "fco.mm"
include "mp2an.mm"
include "trud.mm"
include "feq1i.mm"
include "mpbi.mm"
include "ffvelrni.mm"
include "recnd.mm"
include "nncn.mm"
include "nnne0.mm"
include "divassd.mm"
include "oveq1d.mm"
include "simpr.mm"
include "nndivre.mm"
include "2ne0.mm"
include "divcan3d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "rpne0d.mm"
include "divcan2d.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "eqeltrrd.mm"
include "mulassd.mm"
include "mulcl.mm"
include "mul4d.mm"
include "mul32d.mm"
include "3eqtr2d.mm"
include "syl5eq.mm"
include "3eqtr4d.mm"
include "climmulc2.mm"
include "mulid1i.mm"
include "breqtri.mm"

theorem circum
  let cA: class A
  let cP: class P
  let cR: class R
  let vn: setvar n
  let vy: setvar y
  let vk: setvar k
  assume circum.1: |- A = ( ( 2 x. _pi ) / n )
  assume circum.2: |- P = ( n e. NN |-> ( ( 2 x. n ) x. ( R x. ( sin ` ( A / 2 ) ) ) ) )
  assume circum.3: |- R e. RR

  disjoint R n
  disjoint n y
  disjoint P k
  disjoint k n
  disjoint R k
  assert |- P ~~> ( ( 2 x. _pi ) x. R )

  proof
    cP
    c2
    cpi
    cmul
    co
    #
    cR
    cmul
    co
    #
    c1
    cmul
    co
    #
    @1
    cli
    cP
    @2
    cli
    wbr
    wtru
    c1
    @1
    vk
    vn
    cn
    cpi
    vn
    cv
    #
    cdiv
    co
    #
    csin
    cfv
    #
    @4
    cdiv
    co
    #
    cmpt
    #
    cP
    c1
    cvv
    cn
    nnuz
    wtru
    1zzd
    wtru
    vy
    cr
    cc0
    csn
    #
    cdif
    #
    vy
    cv
    #
    csin
    cfv
    #
    @10
    cdiv
    co
    #
    cmpt
    #
    vn
    cn
    @4
    cmpt
    #
    ccom
    #
    @7
    c1
    cli
    wtru
    vn
    vy
    cn
    @9
    @4
    @12
    @6
    @14
    @13
    @3
    cn
    wcel
    #
    @4
    @9
    wcel
    #
    wtru
    @16
    @4
    cr
    wcel
    @4
    cc0
    wne
    wa
    @17
    @16
    @4
    @16
    cpi
    crp
    wcel
    #
    @3
    crp
    wcel
    @4
    crp
    wcel
    pirp
    @3
    nnrp
    cpi
    @3
    rpdivcl
    sylancr
    rprene0d
    @4
    cr
    cc0
    eldifsn
    sylibr
    #
    adantl
    wtru
    @14
    eqidd
    wtru
    @13
    eqidd
    @10
    @4
    wceq
    #
    @11
    @5
    @10
    @4
    cdiv
    @10
    @4
    csin
    fveq2
    @20
    id
    oveq12d
    fmptco
    #
    wtru
    cn
    @9
    @14
    wf
    #
    @14
    cc0
    cli
    wbr
    #
    @15
    c1
    cli
    wbr
    vn
    cn
    @9
    @4
    @14
    @14
    eqid
    @19
    fmpti
    #
    cpi
    cc
    wcel
    #
    @23
    wtru
    cpi
    pire
    recni
    #
    cpi
    vn
    divcnv
    mp1i
    vy
    @14
    sinccvg
    sylancr
    eqbrtrrd
    @1
    cc
    wcel
    wtru
    @1
    @0
    cR
    c2
    cpi
    2re
    pire
    remulcli
    circum.3
    remulcli
    recni
    #
    a1i
    cP
    cvv
    wcel
    wtru
    cP
    vn
    cn
    c2
    @3
    cmul
    co
    #
    cR
    cA
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cmpt
    cvv
    circum.2
    vn
    cn
    @32
    nnex
    mptex
    eqeltri
    a1i
    wtru
    vk
    cv
    #
    cn
    wcel
    #
    wa
    #
    @33
    @7
    cfv
    #
    @34
    @36
    cr
    wcel
    wtru
    cn
    cr
    @33
    @7
    cn
    cr
    @15
    wf
    #
    cn
    cr
    @7
    wf
    @9
    cr
    @13
    wf
    @22
    @37
    vy
    @9
    cr
    @12
    @13
    @13
    eqid
    @10
    @9
    wcel
    #
    @11
    @10
    @38
    @10
    @10
    cr
    @8
    eldifi
    #
    resincld
    @39
    @10
    cr
    cc0
    eldifsni
    redivcld
    fmpti
    @24
    cn
    @9
    cr
    @13
    @14
    fco
    mp2an
    cn
    cr
    @15
    @7
    @15
    @7
    wceq
    @21
    trud
    feq1i
    mpbi
    ffvelrni
    adantl
    recnd
    #
    @35
    c2
    @33
    cmul
    co
    #
    cR
    @0
    @33
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    @1
    cpi
    @33
    cdiv
    co
    #
    csin
    cfv
    #
    @47
    cdiv
    co
    #
    cmul
    co
    #
    @33
    cP
    cfv
    #
    @1
    @36
    cmul
    co
    @35
    @46
    @41
    cR
    @47
    cmul
    co
    #
    @49
    cmul
    co
    #
    cmul
    co
    @41
    @52
    cmul
    co
    #
    @49
    cmul
    co
    @50
    @35
    @45
    @53
    @41
    cmul
    @35
    @45
    cR
    @47
    @49
    cmul
    co
    #
    cmul
    co
    @53
    @35
    @44
    @55
    cR
    cmul
    @35
    @44
    @48
    @55
    @35
    @43
    @47
    csin
    @35
    @43
    c2
    @47
    cmul
    co
    #
    c2
    cdiv
    co
    @47
    @35
    @42
    @56
    c2
    cdiv
    @35
    c2
    cpi
    @33
    c2
    cc
    wcel
    #
    @35
    c2
    2re
    recni
    #
    a1i
    #
    @25
    @35
    @26
    a1i
    #
    @34
    @33
    cc
    wcel
    #
    wtru
    @33
    nncn
    adantl
    #
    @34
    @33
    cc0
    wne
    wtru
    @33
    nnne0
    adantl
    #
    divassd
    oveq1d
    @35
    @47
    c2
    @35
    @47
    @35
    cpi
    cr
    wcel
    @34
    @47
    cr
    wcel
    pire
    wtru
    @34
    simpr
    cpi
    @33
    nndivre
    sylancr
    #
    recnd
    #
    @59
    c2
    cc0
    wne
    @35
    2ne0
    a1i
    divcan3d
    eqtrd
    fveq2d
    @35
    @48
    @47
    @35
    @48
    @35
    @47
    @64
    resincld
    recnd
    @65
    @35
    @47
    @35
    @18
    @33
    crp
    wcel
    #
    @47
    crp
    wcel
    pirp
    @34
    @66
    wtru
    @33
    nnrp
    adantl
    cpi
    @33
    rpdivcl
    sylancr
    rpne0d
    divcan2d
    eqtr4d
    oveq2d
    @35
    cR
    @47
    @49
    cR
    cc
    wcel
    #
    @35
    cR
    circum.3
    recni
    #
    a1i
    #
    @65
    @35
    @36
    @49
    cc
    @34
    @36
    @49
    wceq
    wtru
    vn
    @33
    @6
    @49
    cn
    @7
    @3
    @33
    wceq
    #
    @5
    @48
    @4
    @47
    cdiv
    @70
    @4
    @47
    csin
    @3
    @33
    cpi
    cdiv
    oveq2
    #
    fveq2d
    @71
    oveq12d
    @7
    eqid
    @48
    @47
    cdiv
    ovex
    fvmpt
    adantl
    #
    @40
    eqeltrrd
    #
    mulassd
    eqtr4d
    oveq2d
    @35
    @41
    @52
    @49
    @35
    @57
    @61
    @41
    cc
    wcel
    @58
    @62
    c2
    @33
    mulcl
    sylancr
    @35
    @67
    @47
    cc
    wcel
    @52
    cc
    wcel
    @68
    @65
    cR
    @47
    mulcl
    sylancr
    @73
    mulassd
    @35
    @54
    @1
    @49
    cmul
    @35
    @54
    c2
    cR
    cmul
    co
    #
    @33
    @47
    cmul
    co
    #
    cmul
    co
    #
    @1
    @35
    c2
    @33
    cR
    @47
    @59
    @62
    @69
    @65
    mul4d
    @35
    @76
    @74
    cpi
    cmul
    co
    @1
    @35
    @75
    cpi
    @74
    cmul
    @35
    cpi
    @33
    @60
    @62
    @63
    divcan2d
    oveq2d
    @35
    c2
    cR
    cpi
    @59
    @69
    @60
    mul32d
    eqtrd
    eqtrd
    oveq1d
    3eqtr2d
    @34
    @51
    @46
    wceq
    wtru
    vn
    @33
    @32
    @46
    cn
    cP
    @70
    @28
    @41
    @31
    @45
    cmul
    @3
    @33
    c2
    cmul
    oveq2
    @70
    @30
    @44
    cR
    cmul
    @70
    @29
    @43
    csin
    @70
    cA
    @42
    c2
    cdiv
    @70
    cA
    @0
    @3
    cdiv
    co
    @42
    circum.1
    @3
    @33
    @0
    cdiv
    oveq2
    syl5eq
    oveq1d
    fveq2d
    oveq2d
    oveq12d
    circum.2
    @41
    @45
    cmul
    ovex
    fvmpt
    adantl
    @35
    @36
    @49
    @1
    cmul
    @72
    oveq2d
    3eqtr4d
    climmulc2
    trud
    @1
    @27
    mulid1i
    breqtri
end
