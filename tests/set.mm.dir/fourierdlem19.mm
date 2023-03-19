include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "cxr.mm"
include "wcel.mm"
include "cioc.mm"
include "readdcld.mm"
include "rexrd.mm"
include "cv.mm"
include "cmul.mm"
include "cz.mm"
include "wrex.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "iocleub.mm"
include "syl3anc.mm"
include "adantr.mm"
include "wa.mm"
include "wn.mm"
include "cr.mm"
include "wss.mm"
include "iocssre.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "cmin.mm"
include "resubcld.mm"
include "syl5eqel.mm"
include "wceq.mm"
include "eqcomi.mm"
include "a1i.mm"
include "recnd.mm"
include "subaddd.mm"
include "mpbid.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "add32d.mm"
include "eqtrd.mm"
include "iocgtlb.mm"
include "ltadd1dd.mm"
include "eqbrtrd.mm"
include "cfv.mm"
include "cdiv.mm"
include "cfl.mm"
include "cc.mm"
include "cmpt.mm"
include "id.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "adantl.mm"
include "cc0.mm"
include "posdifd.mm"
include "syl6breqr.mm"
include "gt0ne0d.mm"
include "redivcld.mm"
include "flcld.mm"
include "zred.mm"
include "remulcld.mm"
include "fvmptd.mm"
include "eqeltrd.mm"
include "subsubd.mm"
include "pncand.mm"
include "c1.mm"
include "adddirp1d.mm"
include "1red.mm"
include "0red.mm"
include "ltled.mm"
include "crp.mm"
include "elrpd.mm"
include "simpr.mm"
include "ltsub2dd.mm"
include "ltdiv1dd.mm"
include "eqtr3d.mm"
include "pncan2d.mm"
include "divcan4d.mm"
include "eqtr2d.mm"
include "3eqtrrd.mm"
include "3brtr4d.mm"
include "wb.mm"
include "zltp1le.mm"
include "lemul1ad.mm"
include "lesub1dd.mm"
include "lesub2dd.mm"
include "subadd2d.mm"
include "mpbird.mm"
include "fourierdlem4.mm"
include "ffvelrnd.mm"
include "ltletrd.mm"
include "ltnled.mm"
include "pm2.65da.mm"

theorem fourierdlem19
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let vk: setvar k
  let cE: class E
  let cW: class W
  let cX: class X
  let cZ: class Z
  assume fourierdlem19.a: |- ( ph -> A e. RR )
  assume fourierdlem19.b: |- ( ph -> B e. RR )
  assume fourierdlem19.altb: |- ( ph -> A < B )
  assume fourierdlem19.x: |- ( ph -> X e. RR )
  assume fourierdlem19.d: |- D = { y e. ( ( A + X ) (,] ( B + X ) ) | E. k e. ZZ ( y + ( k x. T ) ) e. C }
  assume fourierdlem19.t: |- T = ( B - A )
  assume fourierdlem19.e: |- E = ( x e. RR |-> ( x + ( ( |_ ` ( ( B - x ) / T ) ) x. T ) ) )
  assume fourierdlem19.w: |- ( ph -> W e. D )
  assume fourierdlem19.z: |- ( ph -> Z e. D )
  assume fourierdlem19.ezew: |- ( ph -> ( E ` Z ) = ( E ` W ) )

  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint T x
  disjoint W x
  disjoint X y
  disjoint Z x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> -. W < Z )

  proof
    wph
    cW
    cZ
    clt
    wbr
    #
    cZ
    cB
    cX
    caddc
    co
    #
    cle
    wbr
    #
    wph
    @2
    @0
    wph
    cA
    cX
    caddc
    co
    #
    cxr
    wcel
    #
    @1
    cxr
    wcel
    #
    cZ
    @3
    @1
    cioc
    co
    #
    wcel
    @2
    wph
    @3
    wph
    cA
    cX
    fourierdlem19.a
    fourierdlem19.x
    readdcld
    #
    rexrd
    #
    wph
    @1
    wph
    cB
    cX
    fourierdlem19.b
    fourierdlem19.x
    readdcld
    #
    rexrd
    #
    wph
    cD
    @6
    cZ
    cD
    vy
    cv
    vk
    cv
    cT
    cmul
    co
    caddc
    co
    cC
    wcel
    vk
    cz
    wrex
    #
    vy
    @6
    crab
    @6
    fourierdlem19.d
    @11
    vy
    @6
    ssrab2
    eqsstri
    #
    fourierdlem19.z
    sseldi
    #
    @3
    @1
    cZ
    iocleub
    syl3anc
    adantr
    wph
    @0
    wa
    #
    @1
    cZ
    clt
    wbr
    @2
    wn
    @14
    @1
    cW
    cT
    caddc
    co
    #
    cZ
    wph
    @1
    cr
    wcel
    #
    @0
    @9
    adantr
    #
    wph
    @15
    cr
    wcel
    @0
    wph
    cW
    cT
    wph
    @6
    cr
    cW
    wph
    @4
    @16
    @6
    cr
    wss
    @8
    @9
    @3
    @1
    iocssre
    syl2anc
    #
    wph
    cD
    @6
    cW
    @12
    fourierdlem19.w
    sseldi
    #
    sseldd
    #
    wph
    cT
    cB
    cA
    cmin
    co
    #
    cr
    fourierdlem19.t
    wph
    cB
    cA
    fourierdlem19.b
    fourierdlem19.a
    resubcld
    syl5eqel
    #
    readdcld
    adantr
    wph
    cZ
    cr
    wcel
    @0
    wph
    @6
    cr
    cZ
    @18
    @13
    sseldd
    #
    adantr
    #
    wph
    @1
    @15
    clt
    wbr
    @0
    wph
    @1
    @3
    cT
    caddc
    co
    #
    @15
    clt
    wph
    @1
    cA
    cT
    caddc
    co
    #
    cX
    caddc
    co
    @25
    wph
    cB
    @26
    cX
    caddc
    wph
    @26
    cB
    wph
    @21
    cT
    wceq
    #
    @26
    cB
    wceq
    @27
    wph
    cT
    @21
    fourierdlem19.t
    eqcomi
    a1i
    wph
    cB
    cA
    cT
    wph
    cB
    fourierdlem19.b
    recnd
    wph
    cA
    fourierdlem19.a
    recnd
    #
    wph
    cT
    @22
    recnd
    #
    subaddd
    mpbid
    eqcomd
    oveq1d
    wph
    cA
    cT
    cX
    @28
    @29
    wph
    cX
    fourierdlem19.x
    recnd
    add32d
    eqtrd
    wph
    @3
    cW
    cT
    @7
    @20
    @22
    wph
    @4
    @5
    cW
    @6
    wcel
    @3
    cW
    clt
    wbr
    @8
    @10
    @19
    @3
    @1
    cW
    iocgtlb
    syl3anc
    ltadd1dd
    eqbrtrd
    adantr
    @14
    cW
    cE
    cfv
    #
    cB
    cW
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    cmin
    co
    #
    cT
    caddc
    co
    #
    @30
    cB
    cZ
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    cmin
    co
    #
    @15
    cZ
    cle
    @14
    @36
    @30
    @34
    cT
    cmin
    co
    #
    cmin
    co
    #
    @41
    cle
    @14
    @43
    @36
    @14
    @30
    @34
    cT
    wph
    @30
    cc
    wcel
    @0
    wph
    @30
    wph
    @30
    cW
    @34
    caddc
    co
    #
    cr
    wph
    vx
    cW
    vx
    cv
    #
    cB
    @45
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    @44
    cr
    cE
    cr
    cE
    vx
    cr
    @50
    cmpt
    wceq
    wph
    fourierdlem19.e
    a1i
    #
    @45
    cW
    wceq
    #
    @50
    @44
    wceq
    wph
    @52
    @45
    cW
    @49
    @34
    caddc
    @52
    id
    @52
    @48
    @33
    cT
    cmul
    @52
    @47
    @32
    cfl
    @52
    @46
    @31
    cT
    cdiv
    @45
    cW
    cB
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    oveq12d
    adantl
    @20
    wph
    cW
    @34
    @20
    wph
    @33
    cT
    wph
    @33
    wph
    @32
    wph
    @31
    cT
    wph
    cB
    cW
    fourierdlem19.b
    @20
    resubcld
    @22
    wph
    cT
    wph
    cc0
    @21
    cT
    clt
    wph
    cA
    cB
    clt
    wbr
    cc0
    @21
    clt
    wbr
    fourierdlem19.altb
    wph
    cA
    cB
    fourierdlem19.a
    fourierdlem19.b
    posdifd
    mpbid
    fourierdlem19.t
    syl6breqr
    #
    gt0ne0d
    #
    redivcld
    flcld
    #
    zred
    #
    @22
    remulcld
    #
    readdcld
    #
    fvmptd
    #
    @58
    eqeltrd
    #
    recnd
    #
    adantr
    wph
    @34
    cc
    wcel
    @0
    wph
    @34
    @57
    recnd
    #
    adantr
    wph
    cT
    cc
    wcel
    @0
    @29
    adantr
    subsubd
    eqcomd
    @14
    @40
    @42
    @30
    @14
    @39
    cT
    wph
    @39
    cr
    wcel
    @0
    wph
    @39
    wph
    @38
    wph
    @37
    cT
    wph
    cB
    cZ
    fourierdlem19.b
    @23
    resubcld
    @22
    @54
    redivcld
    flcld
    #
    zred
    #
    adantr
    #
    wph
    cT
    cr
    wcel
    @0
    @22
    adantr
    #
    remulcld
    #
    @14
    @34
    cT
    @14
    @33
    cT
    wph
    @33
    cr
    wcel
    @0
    @56
    adantr
    #
    @66
    remulcld
    #
    @66
    resubcld
    wph
    @30
    cr
    wcel
    @0
    @60
    adantr
    #
    @14
    @40
    @40
    cT
    caddc
    co
    #
    cT
    cmin
    co
    #
    @42
    cle
    wph
    @40
    @72
    wceq
    @0
    wph
    @72
    @40
    wph
    @40
    cT
    wph
    @40
    wph
    @39
    cT
    @64
    @22
    remulcld
    #
    recnd
    #
    @29
    pncand
    eqcomd
    adantr
    @14
    @71
    @34
    cT
    @14
    @40
    cT
    @67
    @66
    readdcld
    @69
    @66
    @14
    @71
    @39
    c1
    caddc
    co
    #
    cT
    cmul
    co
    #
    @34
    cle
    wph
    @71
    @76
    wceq
    @0
    wph
    @76
    @71
    wph
    @39
    cT
    wph
    @39
    @64
    recnd
    #
    @29
    adddirp1d
    eqcomd
    adantr
    @14
    @75
    @33
    cT
    @14
    @39
    c1
    @65
    @14
    1red
    readdcld
    @68
    @66
    wph
    cc0
    cT
    cle
    wbr
    @0
    wph
    cc0
    cT
    wph
    0red
    @22
    @53
    ltled
    adantr
    @14
    @39
    @33
    clt
    wbr
    #
    @75
    @33
    cle
    wbr
    #
    @14
    @30
    cZ
    cmin
    co
    #
    cT
    cdiv
    co
    #
    @30
    cW
    cmin
    co
    #
    cT
    cdiv
    co
    #
    @39
    @33
    clt
    @14
    @80
    @82
    cT
    @14
    @30
    cZ
    @70
    @24
    resubcld
    @14
    @30
    cW
    @70
    wph
    cW
    cr
    wcel
    @0
    @20
    adantr
    #
    resubcld
    wph
    cT
    crp
    wcel
    @0
    wph
    cT
    @22
    @53
    elrpd
    adantr
    @14
    cW
    cZ
    @30
    @84
    @24
    @70
    wph
    @0
    simpr
    ltsub2dd
    ltdiv1dd
    wph
    @39
    @81
    wceq
    @0
    wph
    @81
    @40
    cT
    cdiv
    co
    @39
    wph
    @80
    @40
    cT
    cdiv
    wph
    @80
    cZ
    @40
    caddc
    co
    #
    cZ
    cmin
    co
    @40
    wph
    @30
    @85
    cZ
    cmin
    wph
    cZ
    cE
    cfv
    #
    @30
    @85
    fourierdlem19.ezew
    wph
    vx
    cZ
    @50
    @85
    cr
    cE
    cr
    @51
    @45
    cZ
    wceq
    #
    @50
    @85
    wceq
    wph
    @87
    @45
    cZ
    @49
    @40
    caddc
    @87
    id
    @87
    @48
    @39
    cT
    cmul
    @87
    @47
    @38
    cfl
    @87
    @46
    @37
    cT
    cdiv
    @45
    cZ
    cB
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    oveq12d
    adantl
    @23
    wph
    cZ
    @40
    @23
    @73
    readdcld
    fvmptd
    #
    eqtr3d
    oveq1d
    wph
    cZ
    @40
    wph
    cZ
    @23
    recnd
    #
    @74
    pncan2d
    eqtrd
    oveq1d
    wph
    @39
    cT
    @77
    @29
    @54
    divcan4d
    eqtr2d
    adantr
    wph
    @33
    @83
    wceq
    @0
    wph
    @83
    @44
    cW
    cmin
    co
    #
    cT
    cdiv
    co
    @34
    cT
    cdiv
    co
    @33
    wph
    @82
    @90
    cT
    cdiv
    wph
    @30
    @44
    cW
    cmin
    @59
    oveq1d
    oveq1d
    wph
    @90
    @34
    cT
    cdiv
    wph
    cW
    @34
    wph
    cW
    @20
    recnd
    #
    @62
    pncan2d
    oveq1d
    wph
    @33
    cT
    wph
    @33
    @56
    recnd
    @29
    @54
    divcan4d
    3eqtrrd
    adantr
    3brtr4d
    @14
    @39
    cz
    wcel
    #
    @33
    cz
    wcel
    #
    @78
    @79
    wb
    wph
    @92
    @0
    @63
    adantr
    wph
    @93
    @0
    @55
    adantr
    @39
    @33
    zltp1le
    syl2anc
    mpbid
    lemul1ad
    eqbrtrd
    lesub1dd
    eqbrtrd
    lesub2dd
    eqbrtrd
    wph
    @15
    @36
    wceq
    @0
    wph
    cW
    @35
    cT
    caddc
    wph
    @35
    cW
    wph
    @35
    cW
    wceq
    @44
    @30
    wceq
    wph
    @30
    @44
    @59
    eqcomd
    wph
    @30
    @34
    cW
    @61
    @62
    @91
    subadd2d
    mpbird
    eqcomd
    oveq1d
    adantr
    wph
    cZ
    @41
    wceq
    @0
    wph
    @86
    @40
    cmin
    co
    #
    cZ
    @41
    wph
    @94
    cZ
    wceq
    @85
    @86
    wceq
    wph
    @86
    @85
    @88
    eqcomd
    wph
    @86
    @40
    cZ
    wph
    @86
    wph
    cA
    cB
    cioc
    co
    #
    cr
    @86
    wph
    cA
    cxr
    wcel
    cB
    cr
    wcel
    @95
    cr
    wss
    wph
    cA
    fourierdlem19.a
    rexrd
    fourierdlem19.b
    cA
    cB
    iocssre
    syl2anc
    wph
    cr
    @95
    cZ
    cE
    wph
    vx
    cA
    cB
    cT
    cE
    fourierdlem19.a
    fourierdlem19.b
    fourierdlem19.altb
    fourierdlem19.t
    fourierdlem19.e
    fourierdlem4
    @23
    ffvelrnd
    sseldd
    recnd
    @74
    @89
    subadd2d
    mpbird
    wph
    @86
    @30
    @40
    cmin
    fourierdlem19.ezew
    oveq1d
    eqtr3d
    adantr
    3brtr4d
    ltletrd
    @14
    @1
    cZ
    @17
    @24
    ltnled
    mpbid
    pm2.65da
end
