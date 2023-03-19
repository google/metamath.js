include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cr.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cdiv.mm"
include "csin.mm"
include "cfv.mm"
include "cif.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "2re.mm"
include "pire.mm"
include "remulcli.mm"
include "eqeltri.mm"
include "recni.mm"
include "mulid2i.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "a1i.mm"
include "crp.mm"
include "cz.mm"
include "id.mm"
include "ad2antlr.mm"
include "2rp.mm"
include "pirp.mm"
include "rpmulcl.mm"
include "mp2an.mm"
include "1z.mm"
include "modcyc.mm"
include "syl3anc.mm"
include "simpr.mm"
include "3eqtrd.mm"
include "iftrued.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "wn.mm"
include "cneg.mm"
include "iffalse.mm"
include "cc.mm"
include "nncn.mm"
include "halfcn.mm"
include "addcld.mm"
include "adantr.mm"
include "recn.mm"
include "mulcld.mm"
include "sincld.mm"
include "halfcld.mm"
include "wne.mm"
include "dirkerdenne0.mm"
include "adantll.mm"
include "div2negd.mm"
include "mp3an23.mm"
include "eqtrd.mm"
include "neqned.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "fveq2i.mm"
include "oveq12i.mm"
include "syl6eq.mm"
include "syl.mm"
include "adddird.mm"
include "ax-1cn.mm"
include "2cnne0.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "div32.mm"
include "mp3an.mm"
include "2ne0.mm"
include "divcli.mm"
include "divcan3i.mm"
include "oveq2d.mm"
include "adddid.mm"
include "addassd.mm"
include "3eqtr4d.mm"
include "fveq2d.mm"
include "sinppi.mm"
include "simpl.mm"
include "nnzd.mm"
include "sinper.mm"
include "syl2anc.mm"
include "negeqd.mm"
include "divdird.mm"
include "oveq12d.mm"
include "mulneg2d.mm"
include "3eqtrrd.mm"
include "3eqtr2rd.mm"
include "pm2.61dan.mm"
include "readdcld.mm"
include "dirkerval2.mm"
include "sylan2.mm"

theorem dirkerper
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cT: class T
  let vn: setvar n
  let cN: class N
  let vk: setvar k
  assume dirkerper.1: |- D = ( n e. NN |-> ( y e. RR |-> if ( ( y mod ( 2 x. _pi ) ) = 0 , ( ( ( 2 x. n ) + 1 ) / ( 2 x. _pi ) ) , ( ( sin ` ( ( n + ( 1 / 2 ) ) x. y ) ) / ( ( 2 x. _pi ) x. ( sin ` ( y / 2 ) ) ) ) ) ) )
  assume dirkerper.2: |- T = ( 2 x. _pi )

  disjoint N y
  disjoint n y
  disjoint k x
  assert |- ( ( N e. NN /\ x e. RR ) -> ( ( D ` N ) ` ( x + T ) ) = ( ( D ` N ) ` x ) )

  proof
    cN
    cn
    wcel
    #
    vx
    cv
    #
    cr
    wcel
    #
    wa
    #
    @1
    cT
    caddc
    co
    #
    c2
    cpi
    cmul
    co
    #
    cmo
    co
    #
    cc0
    wceq
    #
    c2
    cN
    cmul
    co
    c1
    caddc
    co
    @5
    cdiv
    co
    #
    cN
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @4
    cmul
    co
    #
    csin
    cfv
    #
    @5
    @4
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
    cdiv
    co
    #
    cif
    #
    @1
    @5
    cmo
    co
    #
    cc0
    wceq
    #
    @8
    @10
    @1
    cmul
    co
    #
    csin
    cfv
    #
    @5
    @1
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
    cdiv
    co
    #
    cif
    #
    @4
    cN
    cD
    cfv
    #
    cfv
    #
    @1
    @27
    cfv
    @3
    @19
    @17
    @26
    wceq
    @3
    @19
    wa
    #
    @17
    @8
    @26
    @29
    @7
    @8
    @16
    @29
    @6
    @1
    c1
    @5
    cmul
    co
    #
    caddc
    co
    #
    @5
    cmo
    co
    #
    @18
    cc0
    @6
    @32
    wceq
    #
    @29
    @4
    @31
    @5
    cmo
    @31
    @4
    @30
    cT
    @1
    caddc
    @30
    c1
    cT
    cmul
    co
    cT
    @5
    cT
    c1
    cmul
    cT
    @5
    dirkerper.2
    eqcomi
    oveq2i
    cT
    cT
    cT
    @5
    cr
    dirkerper.2
    c2
    cpi
    2re
    pire
    remulcli
    #
    eqeltri
    #
    recni
    mulid2i
    eqtri
    oveq2i
    eqcomi
    oveq1i
    #
    a1i
    @29
    @2
    @5
    crp
    wcel
    #
    c1
    cz
    wcel
    #
    @32
    @18
    wceq
    #
    @2
    @2
    @0
    @19
    @2
    id
    #
    ad2antlr
    @37
    @29
    c2
    crp
    wcel
    cpi
    crp
    wcel
    @37
    2rp
    pirp
    c2
    cpi
    rpmulcl
    mp2an
    #
    a1i
    @38
    @29
    1z
    a1i
    @1
    @5
    c1
    modcyc
    #
    syl3anc
    @3
    @19
    simpr
    3eqtrd
    iftrued
    @19
    @26
    @8
    wceq
    @3
    @19
    @8
    @25
    iftrue
    adantl
    eqtr4d
    @3
    @19
    wn
    #
    wa
    #
    @26
    @25
    @21
    cneg
    #
    @24
    cneg
    #
    cdiv
    co
    #
    @17
    @43
    @26
    @25
    wceq
    @3
    @19
    @8
    @25
    iffalse
    adantl
    @44
    @21
    @24
    @3
    @21
    cc
    wcel
    @43
    @3
    @20
    @3
    @10
    @1
    @0
    @10
    cc
    wcel
    @2
    @0
    cN
    @9
    cN
    nncn
    #
    @9
    cc
    wcel
    @0
    halfcn
    a1i
    #
    addcld
    adantr
    #
    @2
    @1
    cc
    wcel
    @0
    @1
    recn
    #
    adantl
    #
    mulcld
    #
    sincld
    adantr
    @3
    @24
    cc
    wcel
    @43
    @3
    @5
    @23
    @5
    cc
    wcel
    #
    @3
    @5
    @34
    recni
    #
    a1i
    #
    @3
    @22
    @3
    @1
    @52
    halfcld
    sincld
    mulcld
    adantr
    @2
    @43
    @24
    cc0
    wne
    @0
    @1
    dirkerdenne0
    adantll
    div2negd
    @44
    @17
    @10
    @1
    @5
    caddc
    co
    #
    cmul
    co
    #
    csin
    cfv
    #
    @5
    @57
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
    cdiv
    co
    #
    @45
    @5
    @23
    cneg
    #
    cmul
    co
    #
    cdiv
    co
    #
    @47
    @2
    @43
    @17
    @63
    wceq
    #
    @0
    @2
    @43
    wa
    #
    @7
    wn
    #
    @67
    @68
    @6
    cc0
    @68
    @6
    @18
    cc0
    @2
    @6
    @18
    wceq
    @43
    @2
    @6
    @32
    @18
    @33
    @2
    @36
    a1i
    @2
    @37
    @38
    @39
    @41
    1z
    @42
    mp3an23
    eqtrd
    adantr
    @68
    @18
    cc0
    @2
    @43
    simpr
    neqned
    eqnetrd
    neneqd
    @69
    @17
    @16
    @63
    @7
    @8
    @16
    iffalse
    @12
    @59
    @15
    @62
    cdiv
    @11
    @58
    csin
    @4
    @57
    @10
    cmul
    cT
    @5
    @1
    caddc
    dirkerper.2
    oveq2i
    #
    oveq2i
    fveq2i
    @14
    @61
    @5
    cmul
    @13
    @60
    csin
    @4
    @57
    c2
    cdiv
    @70
    oveq1i
    fveq2i
    oveq2i
    oveq12i
    syl6eq
    syl
    adantll
    @3
    @63
    @66
    wceq
    @43
    @3
    @59
    @45
    @62
    @65
    cdiv
    @3
    @59
    @20
    cN
    @5
    cmul
    co
    #
    caddc
    co
    #
    cpi
    caddc
    co
    #
    csin
    cfv
    #
    @72
    csin
    cfv
    #
    cneg
    #
    @45
    @3
    @58
    @73
    csin
    @3
    @20
    @10
    @5
    cmul
    co
    #
    caddc
    co
    #
    @20
    @71
    cpi
    caddc
    co
    #
    caddc
    co
    #
    @58
    @73
    @0
    @78
    @80
    wceq
    @2
    @0
    @77
    @79
    @20
    caddc
    @0
    @77
    @71
    @9
    @5
    cmul
    co
    #
    caddc
    co
    @79
    @0
    cN
    @9
    @5
    @48
    @49
    @54
    @0
    @55
    a1i
    #
    adddird
    @81
    cpi
    @71
    caddc
    @81
    c1
    @5
    c2
    cdiv
    co
    #
    cmul
    co
    #
    cpi
    c1
    cc
    wcel
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    wa
    @54
    @81
    @84
    wceq
    ax-1cn
    2cnne0
    c2
    cpi
    2cn
    picn
    mulcli
    #
    c1
    c2
    @5
    div32
    mp3an
    @84
    @83
    cpi
    @83
    @5
    c2
    @87
    2cn
    2ne0
    divcli
    mulid2i
    cpi
    c2
    picn
    2cn
    2ne0
    divcan3i
    #
    eqtri
    eqtri
    oveq2i
    syl6eq
    oveq2d
    adantr
    @3
    @10
    @1
    @5
    @50
    @52
    @56
    adddid
    @3
    @20
    @71
    cpi
    @53
    @0
    @71
    cc
    wcel
    @2
    @0
    cN
    @5
    @48
    @82
    mulcld
    adantr
    #
    cpi
    cc
    wcel
    @3
    picn
    a1i
    addassd
    3eqtr4d
    fveq2d
    @3
    @72
    cc
    wcel
    @74
    @76
    wceq
    @3
    @20
    @71
    @53
    @89
    addcld
    @72
    sinppi
    syl
    @3
    @75
    @21
    @3
    @20
    cc
    wcel
    cN
    cz
    wcel
    @75
    @21
    wceq
    @53
    @3
    cN
    @0
    @2
    simpl
    nnzd
    @20
    cN
    sinper
    syl2anc
    negeqd
    3eqtrd
    @2
    @62
    @65
    wceq
    @0
    @2
    @61
    @64
    @5
    cmul
    @2
    @61
    @22
    cpi
    caddc
    co
    #
    csin
    cfv
    #
    @64
    @2
    @60
    @90
    csin
    @2
    @60
    @22
    @83
    caddc
    co
    @90
    @2
    @1
    @5
    c2
    @51
    @54
    @2
    @55
    a1i
    #
    @85
    @2
    2cn
    a1i
    @86
    @2
    2ne0
    a1i
    divdird
    @2
    @83
    cpi
    @22
    caddc
    @83
    cpi
    wceq
    @2
    @88
    a1i
    oveq2d
    eqtrd
    fveq2d
    @2
    @22
    cc
    wcel
    @91
    @64
    wceq
    @2
    @1
    @51
    halfcld
    #
    @22
    sinppi
    syl
    eqtrd
    oveq2d
    adantl
    oveq12d
    adantr
    @2
    @66
    @47
    wceq
    @0
    @43
    @2
    @65
    @46
    @45
    cdiv
    @2
    @5
    @23
    @92
    @2
    @22
    @93
    sincld
    mulneg2d
    oveq2d
    ad2antlr
    3eqtrrd
    3eqtr2rd
    pm2.61dan
    @2
    @0
    @4
    cr
    wcel
    @28
    @17
    wceq
    @2
    @1
    cT
    @40
    cT
    cr
    wcel
    @2
    @35
    a1i
    readdcld
    cD
    @4
    vn
    cN
    vy
    dirkerper.1
    dirkerval2
    sylan2
    cD
    @1
    vn
    cN
    vy
    dirkerper.1
    dirkerval2
    3eqtr4d
end
