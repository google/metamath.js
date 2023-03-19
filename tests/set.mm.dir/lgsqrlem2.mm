include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cfz.mm"
include "cfv.mm"
include "ccnv.mm"
include "c0g.mm"
include "csn.mm"
include "cima.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "cexp.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cz.mm"
include "zring.mm"
include "crh.mm"
include "crg.mm"
include "ccrg.mm"
include "cidom.mm"
include "cfield.mm"
include "cprime.mm"
include "eldifad.mm"
include "znfld.mm"
include "syl.mm"
include "fldidom.mm"
include "cdomn.mm"
include "isidom.mm"
include "simplbi.mm"
include "crngring.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "eqid.mm"
include "rhmf.mm"
include "adantr.mm"
include "elfzelz.mm"
include "adantl.mm"
include "zsqcl.mm"
include "ffvelrnd.mm"
include "cdif.mm"
include "cmo.mm"
include "cphi.mm"
include "cmul.mm"
include "cn.mm"
include "elfznn.mm"
include "nncnd.mm"
include "cn0.mm"
include "oddprm.mm"
include "nnnn0d.mm"
include "2nn0.mm"
include "a1i.mm"
include "expmuld.mm"
include "cr.mm"
include "prmnn.mm"
include "nnred.mm"
include "peano2rem.mm"
include "recnd.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan2d.mm"
include "phiprm.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "cgcd.mm"
include "nnzd.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cle.mm"
include "clt.mm"
include "rehalfcld.mm"
include "elfzle2.mm"
include "crp.mm"
include "cuz.mm"
include "prmuz2.mm"
include "uz2m1nn.mm"
include "nnrpd.mm"
include "rphalflt.mm"
include "ltm1d.mm"
include "lttrd.mm"
include "lelttrd.mm"
include "ltnled.mm"
include "mpbid.mm"
include "dvdsle.mm"
include "mtod.mm"
include "wb.mm"
include "coprm.mm"
include "eqtrd.mm"
include "eulerth.mm"
include "syl3anc.mm"
include "lgsqrlem1.mm"
include "wfn.mm"
include "cpws.mm"
include "cvv.mm"
include "fvexd.mm"
include "evl1rhm.mm"
include "cgrp.mm"
include "ply1ring.mm"
include "ringgrp.mm"
include "cmgp.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "ringidcl.mm"
include "grpsubcl.mm"
include "syl5eqel.mm"
include "pwselbas.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mpbir2and.mm"
include "fmptd.mm"
include "caddc.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "eqeq12d.mm"
include "zndvds.mm"
include "cc.mm"
include "subsq.mm"
include "breq2d.mm"
include "3bitrd.mm"
include "wo.mm"
include "zaddcld.mm"
include "zsubcld.mm"
include "euclemma.mm"
include "nnaddcld.mm"
include "le2addd.mm"
include "2halvesd.mm"
include "breqtrd.mm"
include "pm2.21d.mm"
include "syld.mm"
include "moddvds.mm"
include "nn0ge0d.mm"
include "modid.mm"
include "syl22anc.mm"
include "bitr3d.mm"
include "biimpd.mm"
include "jaod.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem lgsqrlem2
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cD: class D
  let cP: class P
  let cS: class S
  let cT: class T
  let c.1: class .1.
  let c.ex: class .^
  let cG: class G
  let cL: class L
  let c.mi: class .-
  let cO: class O
  let cX: class X
  let cY: class Y
  let cA: class A
  let vx: setvar x
  let vz: setvar z
  assume lgsqr.y: |- Y = ( Z/nZ ` P )
  assume lgsqr.s: |- S = ( Poly1 ` Y )
  assume lgsqr.b: |- B = ( Base ` S )
  assume lgsqr.d: |- D = ( deg1 ` Y )
  assume lgsqr.o: |- O = ( eval1 ` Y )
  assume lgsqr.e: |- .^ = ( .g ` ( mulGrp ` S ) )
  assume lgsqr.x: |- X = ( var1 ` Y )
  assume lgsqr.m: |- .- = ( -g ` S )
  assume lgsqr.u: |- .1. = ( 1r ` S )
  assume lgsqr.t: |- T = ( ( ( ( P - 1 ) / 2 ) .^ X ) .- .1. )
  assume lgsqr.l: |- L = ( ZRHom ` Y )
  assume lgsqr.1: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume lgsqr.g: |- G = ( y e. ( 1 ... ( ( P - 1 ) / 2 ) ) |-> ( L ` ( y ^ 2 ) ) )

  disjoint O y
  disjoint P y
  disjoint ph y
  disjoint T y
  disjoint L y
  disjoint Y y
  disjoint A x
  disjoint x z
  disjoint G x
  disjoint G z
  disjoint x y
  disjoint P x
  disjoint y z
  disjoint P z
  disjoint ph x
  disjoint ph z
  disjoint L x
  disjoint Y x
  assert |- ( ph -> G : ( 1 ... ( ( P - 1 ) / 2 ) ) -1-1-> ( `' ( O ` T ) " { ( 0g ` Y ) } ) )

  proof
    wph
    c1
    cP
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cfz
    co
    #
    cT
    cO
    cfv
    #
    ccnv
    cY
    c0g
    cfv
    #
    csn
    cima
    #
    cG
    wf
    vx
    cv
    #
    cG
    cfv
    #
    vz
    cv
    #
    cG
    cfv
    #
    wceq
    #
    @6
    @8
    wceq
    #
    wi
    #
    vz
    @2
    wral
    vx
    @2
    wral
    @2
    @5
    cG
    wf1
    wph
    vy
    @2
    vy
    cv
    #
    c2
    cexp
    co
    #
    cL
    cfv
    #
    @5
    cG
    wph
    @13
    @2
    wcel
    #
    wa
    #
    @15
    @5
    wcel
    #
    @15
    cY
    cbs
    cfv
    #
    wcel
    #
    @15
    @3
    cfv
    @4
    wceq
    #
    @17
    cz
    @19
    @14
    cL
    wph
    cz
    @19
    cL
    wf
    #
    @16
    wph
    cL
    zring
    cY
    crh
    co
    wcel
    #
    @22
    wph
    cY
    crg
    wcel
    #
    @23
    wph
    cY
    ccrg
    wcel
    #
    @24
    wph
    cY
    cidom
    wcel
    #
    @25
    wph
    cY
    cfield
    wcel
    #
    @26
    wph
    cP
    cprime
    wcel
    #
    @27
    wph
    cP
    cprime
    c2
    csn
    #
    lgsqr.1
    eldifad
    #
    cP
    cY
    lgsqr.y
    znfld
    syl
    #
    cY
    fldidom
    syl
    @26
    @25
    cY
    cdomn
    wcel
    cY
    isidom
    simplbi
    syl
    #
    cY
    crngring
    syl
    #
    cY
    cL
    lgsqr.l
    zrhrhm
    syl
    cz
    @19
    zring
    cY
    cL
    zringbas
    @19
    eqid
    #
    rhmf
    syl
    adantr
    @17
    @13
    cz
    wcel
    #
    @14
    cz
    wcel
    @16
    @35
    wph
    @13
    c1
    @1
    elfzelz
    adantl
    #
    @13
    zsqcl
    syl
    #
    ffvelrnd
    @17
    @14
    cB
    cD
    cP
    cS
    cT
    c.1
    c.ex
    cL
    c.mi
    cO
    cX
    cY
    lgsqr.y
    lgsqr.s
    lgsqr.b
    lgsqr.d
    lgsqr.o
    lgsqr.e
    lgsqr.x
    lgsqr.m
    lgsqr.u
    lgsqr.t
    lgsqr.l
    wph
    cP
    cprime
    @29
    cdif
    wcel
    #
    @16
    lgsqr.1
    adantr
    @37
    @17
    @14
    @1
    cexp
    co
    #
    cP
    cmo
    co
    @13
    cP
    cphi
    cfv
    #
    cexp
    co
    #
    cP
    cmo
    co
    #
    c1
    cP
    cmo
    co
    #
    @17
    @39
    @41
    cP
    cmo
    @17
    @13
    c2
    @1
    cmul
    co
    #
    cexp
    co
    @39
    @41
    @17
    @13
    c2
    @1
    @17
    @13
    @16
    @13
    cn
    wcel
    #
    wph
    @13
    @1
    elfznn
    adantl
    #
    nncnd
    wph
    @1
    cn0
    wcel
    #
    @16
    wph
    @1
    wph
    @38
    @1
    cn
    wcel
    lgsqr.1
    cP
    oddprm
    syl
    nnnn0d
    #
    adantr
    c2
    cn0
    wcel
    @17
    2nn0
    a1i
    expmuld
    @17
    @44
    @40
    @13
    cexp
    wph
    @44
    @40
    wceq
    @16
    wph
    @44
    @0
    @40
    wph
    @0
    c2
    wph
    @0
    wph
    cP
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    wph
    cP
    wph
    @28
    cP
    cn
    wcel
    #
    @30
    cP
    prmnn
    #
    syl
    #
    nnred
    #
    cP
    peano2rem
    #
    syl
    #
    recnd
    #
    wph
    2cnd
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    divcan2d
    wph
    @28
    @40
    @0
    wceq
    @30
    cP
    phiprm
    syl
    eqtr4d
    adantr
    oveq2d
    eqtr3d
    oveq1d
    @17
    @51
    @35
    @13
    cP
    cgcd
    co
    #
    c1
    wceq
    @42
    @43
    wceq
    @17
    @28
    @51
    wph
    @28
    @16
    @30
    adantr
    #
    @52
    syl
    @36
    @17
    @58
    cP
    @13
    cgcd
    co
    #
    c1
    @17
    @35
    cP
    cz
    wcel
    #
    @58
    @60
    wceq
    @36
    wph
    @61
    @16
    wph
    cP
    @53
    nnzd
    adantr
    #
    @13
    cP
    gcdcom
    syl2anc
    @17
    cP
    @13
    cdvds
    wbr
    #
    wn
    #
    @60
    c1
    wceq
    #
    @17
    @63
    cP
    @13
    cle
    wbr
    #
    @17
    @13
    cP
    clt
    wbr
    @66
    wn
    @17
    @13
    @1
    cP
    @17
    @13
    @46
    nnred
    #
    wph
    @1
    cr
    wcel
    #
    @16
    wph
    @0
    @56
    rehalfcld
    #
    adantr
    wph
    @49
    @16
    @54
    adantr
    #
    @16
    @13
    @1
    cle
    wbr
    wph
    @13
    c1
    @1
    elfzle2
    adantl
    wph
    @1
    cP
    clt
    wbr
    #
    @16
    wph
    @1
    @0
    cP
    @69
    @56
    @54
    wph
    @0
    crp
    wcel
    @1
    @0
    clt
    wbr
    wph
    @0
    wph
    cP
    c2
    cuz
    cfv
    wcel
    #
    @0
    cn
    wcel
    wph
    @28
    @72
    @30
    cP
    prmuz2
    syl
    cP
    uz2m1nn
    syl
    nnrpd
    @0
    rphalflt
    syl
    wph
    cP
    @54
    ltm1d
    lttrd
    #
    adantr
    lelttrd
    @17
    @13
    cP
    @67
    @70
    ltnled
    mpbid
    @17
    @61
    @45
    @63
    @66
    wi
    @62
    @46
    cP
    @13
    dvdsle
    syl2anc
    mtod
    @17
    @28
    @35
    @64
    @65
    wb
    @59
    @36
    cP
    @13
    coprm
    syl2anc
    mpbid
    eqtrd
    @13
    cP
    eulerth
    syl3anc
    eqtrd
    lgsqrlem1
    @17
    @3
    @19
    wfn
    #
    @18
    @20
    @21
    wa
    wb
    wph
    @74
    @16
    wph
    @19
    @19
    @3
    wf
    @74
    wph
    @19
    cY
    @19
    cY
    @19
    cpws
    co
    #
    cbs
    cfv
    #
    cfield
    @3
    @75
    cvv
    @75
    eqid
    #
    @34
    @76
    eqid
    #
    @31
    wph
    cY
    cbs
    fvexd
    wph
    cB
    @76
    cT
    cO
    wph
    cO
    cS
    @75
    crh
    co
    wcel
    #
    cB
    @76
    cO
    wf
    wph
    @25
    @79
    @32
    @19
    cS
    cY
    @75
    cO
    lgsqr.o
    lgsqr.s
    @77
    @34
    evl1rhm
    syl
    cB
    @76
    cS
    @75
    cO
    lgsqr.b
    @78
    rhmf
    syl
    wph
    cT
    @1
    cX
    c.ex
    co
    #
    c.1
    c.mi
    co
    #
    cB
    lgsqr.t
    wph
    cS
    cgrp
    wcel
    #
    @80
    cB
    wcel
    #
    c.1
    cB
    wcel
    #
    @81
    cB
    wcel
    wph
    cS
    crg
    wcel
    #
    @82
    wph
    @24
    @85
    @33
    cS
    cY
    lgsqr.s
    ply1ring
    syl
    #
    cS
    ringgrp
    syl
    wph
    cS
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @47
    cX
    cB
    wcel
    #
    @83
    wph
    @85
    @88
    @86
    cS
    @87
    @87
    eqid
    #
    ringmgp
    syl
    @48
    wph
    @24
    @89
    @33
    cB
    cS
    cY
    cX
    lgsqr.x
    lgsqr.s
    lgsqr.b
    vr1cl
    syl
    cB
    c.ex
    @87
    @1
    cX
    cB
    cS
    @87
    @90
    lgsqr.b
    mgpbas
    lgsqr.e
    mulgnn0cl
    syl3anc
    wph
    @85
    @84
    @86
    cB
    cS
    c.1
    lgsqr.b
    lgsqr.u
    ringidcl
    syl
    cB
    cS
    c.mi
    @80
    c.1
    lgsqr.b
    lgsqr.m
    grpsubcl
    syl3anc
    syl5eqel
    ffvelrnd
    pwselbas
    @19
    @19
    @3
    ffn
    syl
    adantr
    @19
    @4
    @15
    @3
    fniniseg
    syl
    mpbir2and
    lgsqr.g
    fmptd
    wph
    @12
    vx
    vz
    @2
    @2
    wph
    @6
    @2
    wcel
    #
    @8
    @2
    wcel
    #
    wa
    #
    wa
    #
    @10
    cP
    @6
    @8
    caddc
    co
    #
    @6
    @8
    cmin
    co
    #
    cmul
    co
    #
    cdvds
    wbr
    #
    @11
    @94
    @10
    @6
    c2
    cexp
    co
    #
    cL
    cfv
    #
    @8
    c2
    cexp
    co
    #
    cL
    cfv
    #
    wceq
    #
    cP
    @99
    @101
    cmin
    co
    #
    cdvds
    wbr
    #
    @98
    @94
    @7
    @100
    @9
    @102
    @91
    @7
    @100
    wceq
    wph
    @92
    vy
    @6
    @15
    @100
    @2
    cG
    @13
    @6
    wceq
    @14
    @99
    cL
    @13
    @6
    c2
    cexp
    oveq1
    fveq2d
    lgsqr.g
    @99
    cL
    fvex
    fvmpt
    ad2antrl
    @92
    @9
    @102
    wceq
    wph
    @91
    vy
    @8
    @15
    @102
    @2
    cG
    @13
    @8
    wceq
    @14
    @101
    cL
    @13
    @8
    c2
    cexp
    oveq1
    fveq2d
    lgsqr.g
    @101
    cL
    fvex
    fvmpt
    ad2antll
    eqeq12d
    @94
    cP
    cn0
    wcel
    #
    @99
    cz
    wcel
    #
    @101
    cz
    wcel
    #
    @103
    @105
    wb
    wph
    @106
    @93
    wph
    cP
    @53
    nnnn0d
    adantr
    @94
    @6
    cz
    wcel
    #
    @107
    @91
    @109
    wph
    @92
    @6
    c1
    @1
    elfzelz
    ad2antrl
    #
    @6
    zsqcl
    syl
    @94
    @8
    cz
    wcel
    #
    @108
    @92
    @111
    wph
    @91
    @8
    c1
    @1
    elfzelz
    ad2antll
    #
    @8
    zsqcl
    syl
    @99
    @101
    cL
    cP
    cY
    lgsqr.y
    lgsqr.l
    zndvds
    syl3anc
    @94
    @104
    @97
    cP
    cdvds
    @94
    @6
    cc
    wcel
    @8
    cc
    wcel
    @104
    @97
    wceq
    @94
    @6
    @91
    @6
    cn
    wcel
    wph
    @92
    @6
    @1
    elfznn
    ad2antrl
    #
    nncnd
    @94
    @8
    @92
    @8
    cn
    wcel
    wph
    @91
    @8
    @1
    elfznn
    ad2antll
    #
    nncnd
    @6
    @8
    subsq
    syl2anc
    breq2d
    3bitrd
    @94
    @98
    cP
    @95
    cdvds
    wbr
    #
    cP
    @96
    cdvds
    wbr
    #
    wo
    #
    @11
    @94
    @28
    @95
    cz
    wcel
    @96
    cz
    wcel
    @98
    @117
    wb
    wph
    @28
    @93
    @30
    adantr
    #
    @94
    @6
    @8
    @110
    @112
    zaddcld
    @94
    @6
    @8
    @110
    @112
    zsubcld
    cP
    @95
    @96
    euclemma
    syl3anc
    @94
    @115
    @11
    @116
    @94
    @115
    cP
    @95
    cle
    wbr
    #
    @11
    @94
    @61
    @95
    cn
    wcel
    @115
    @119
    wi
    @94
    cP
    @94
    @28
    @51
    @118
    @52
    syl
    #
    nnzd
    @94
    @6
    @8
    @113
    @114
    nnaddcld
    #
    cP
    @95
    dvdsle
    syl2anc
    @94
    @119
    @11
    @94
    @95
    cP
    clt
    wbr
    @119
    wn
    @94
    @95
    @0
    cP
    @94
    @95
    @121
    nnred
    #
    @94
    @49
    @50
    @94
    cP
    @120
    nnred
    #
    @55
    syl
    @123
    @94
    @95
    @1
    @1
    caddc
    co
    @0
    cle
    @94
    @6
    @8
    @1
    @1
    @94
    @6
    @113
    nnred
    #
    @94
    @8
    @114
    nnred
    #
    wph
    @68
    @93
    @69
    adantr
    #
    @126
    @91
    @6
    @1
    cle
    wbr
    wph
    @92
    @6
    c1
    @1
    elfzle2
    ad2antrl
    #
    @92
    @8
    @1
    cle
    wbr
    wph
    @91
    @8
    c1
    @1
    elfzle2
    ad2antll
    #
    le2addd
    @94
    @0
    wph
    @0
    cc
    wcel
    @93
    @57
    adantr
    2halvesd
    breqtrd
    @94
    cP
    @123
    ltm1d
    lelttrd
    @94
    @95
    cP
    @122
    @123
    ltnled
    mpbid
    pm2.21d
    syld
    @94
    @116
    @11
    @94
    @6
    cP
    cmo
    co
    #
    @8
    cP
    cmo
    co
    #
    wceq
    #
    @116
    @11
    @94
    @51
    @109
    @111
    @131
    @116
    wb
    @120
    @110
    @112
    @6
    @8
    cP
    moddvds
    syl3anc
    @94
    @129
    @6
    @130
    @8
    @94
    @6
    cr
    wcel
    cP
    crp
    wcel
    #
    cc0
    @6
    cle
    wbr
    @6
    cP
    clt
    wbr
    @129
    @6
    wceq
    @124
    @94
    cP
    @120
    nnrpd
    #
    @94
    @6
    @94
    @6
    @113
    nnnn0d
    nn0ge0d
    @94
    @6
    @1
    cP
    @124
    @126
    @123
    @127
    wph
    @71
    @93
    @73
    adantr
    #
    lelttrd
    @6
    cP
    modid
    syl22anc
    @94
    @8
    cr
    wcel
    @132
    cc0
    @8
    cle
    wbr
    @8
    cP
    clt
    wbr
    @130
    @8
    wceq
    @125
    @133
    @94
    @8
    @94
    @8
    @114
    nnnn0d
    nn0ge0d
    @94
    @8
    @1
    cP
    @125
    @126
    @123
    @128
    @134
    lelttrd
    @8
    cP
    modid
    syl22anc
    eqeq12d
    bitr3d
    biimpd
    jaod
    sylbid
    sylbid
    ralrimivva
    vx
    vz
    @2
    @5
    cG
    dff13
    sylanbrc
end
