include "wss.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cdprd.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "ssid.mm"
include "cfn.mm"
include "wcel.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "cun.mm"
include "wceq.mm"
include "sseq1.mm"
include "difeq1.mm"
include "0dif.mm"
include "syl6eq.mm"
include "reseq2d.mm"
include "res0.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "notbid.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "c1.mm"
include "cprime.mm"
include "nprmdvds1.mm"
include "syl.mm"
include "c0g.mm"
include "cdm.mm"
include "cabl.mm"
include "cgrp.mm"
include "wa.mm"
include "ablgrp.mm"
include "eqid.mm"
include "dprd0.mm"
include "3syl.mm"
include "simprd.mm"
include "cvv.mm"
include "fvex.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "mtbird.mm"
include "a1d.mm"
include "ssun1.mm"
include "sstr.mm"
include "mpan.mm"
include "imim1i.mm"
include "wo.mm"
include "cmul.mm"
include "clsm.mm"
include "csubg.mm"
include "wf.mm"
include "simpld.mm"
include "dprdf2.mm"
include "adantr.mm"
include "simprr.mm"
include "ssdifssd.mm"
include "fssresd.mm"
include "cin.mm"
include "simprl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "difeq1d.mm"
include "difindir.mm"
include "3eqtr3g.mm"
include "difundir.mm"
include "a1i.mm"
include "dprdres.mm"
include "dprdsplit.mm"
include "ccntz.mm"
include "fdm.mm"
include "ssdif.mm"
include "mp1i.mm"
include "dprdsubg.mm"
include "ssun2.mm"
include "dprddisj2.mm"
include "dprdcntz2.mm"
include "dprdssv.mm"
include "ssfi.mm"
include "sylancl.mm"
include "lsmhash.mm"
include "resabs1d.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "cz.mm"
include "wb.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0zd.mm"
include "euclemma.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "sneqd.mm"
include "difid.mm"
include "eqtrd.mm"
include "wne.mm"
include "cexp.mm"
include "unssbd.mm"
include "vex.mm"
include "snss.mm"
include "sseldd.mm"
include "syldan.mm"
include "prmdvdsexpr.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "necon3ad.mm"
include "imp.mm"
include "disjsn2.mm"
include "adantl.mm"
include "disj3.mm"
include "sylib.mm"
include "dpjlem.mm"
include "eqtr3d.mm"
include "pm2.61dane.mm"
include "orel2.mm"
include "sylbid.mm"
include "con3d.mm"
include "expr.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpi.mm"

theorem ablfac1eulem
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let cT: class T
  let cG: class G
  let cO: class O
  let vq: setvar q
  let vp: setvar p
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  assume ablfac1.b: |- B = ( Base ` G )
  assume ablfac1.o: |- O = ( od ` G )
  assume ablfac1.s: |- S = ( p e. A |-> { x e. B | ( O ` x ) || ( p ^ ( p pCnt ( # ` B ) ) ) } )
  assume ablfac1.g: |- ( ph -> G e. Abel )
  assume ablfac1.f: |- ( ph -> B e. Fin )
  assume ablfac1.1: |- ( ph -> A C_ Prime )
  assume ablfac1c.d: |- D = { w e. Prime | w || ( # ` B ) }
  assume ablfac1.2: |- ( ph -> D C_ A )
  assume ablfac1eu.1: |- ( ph -> ( G dom DProd T /\ ( G DProd T ) = B ) )
  assume ablfac1eu.2: |- ( ph -> dom T = A )
  assume ablfac1eu.3: |- ( ( ph /\ q e. A ) -> C e. NN0 )
  assume ablfac1eu.4: |- ( ( ph /\ q e. A ) -> ( # ` ( T ` q ) ) = ( q ^ C ) )
  assume ablfac1eulem.1: |- ( ph -> P e. Prime )
  assume ablfac1eulem.2: |- ( ph -> A e. Fin )

  disjoint p q
  disjoint p w
  disjoint p x
  disjoint B p
  disjoint q w
  disjoint q x
  disjoint B q
  disjoint w x
  disjoint B w
  disjoint B x
  disjoint D p
  disjoint D q
  disjoint D x
  disjoint p ph
  disjoint ph q
  disjoint ph w
  disjoint ph x
  disjoint S q
  disjoint A p
  disjoint A q
  disjoint A x
  disjoint O p
  disjoint O q
  disjoint O x
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint T q
  disjoint T x
  disjoint G p
  disjoint G q
  disjoint G x
  disjoint p y
  disjoint q y
  disjoint w y
  disjoint x y
  disjoint B y
  disjoint D y
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint b p
  disjoint b q
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b ph
  disjoint p z
  disjoint q z
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint S a
  disjoint S b
  disjoint A a
  disjoint A b
  disjoint A y
  disjoint A z
  disjoint O y
  disjoint P y
  disjoint P z
  disjoint T y
  disjoint T z
  disjoint G a
  disjoint G b
  disjoint G y
  disjoint G z
  assert |- ( ph -> -. P || ( # ` ( G DProd ( T |` ( A \ { P } ) ) ) ) )

  proof
    wph
    cA
    cA
    wss
    #
    cP
    cG
    cT
    cA
    cP
    csn
    #
    cdif
    #
    cres
    #
    cdprd
    co
    #
    chash
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    cA
    ssid
    cA
    cfn
    wcel
    wph
    @0
    @7
    wi
    #
    ablfac1eulem.2
    wph
    vy
    cv
    #
    cA
    wss
    #
    cP
    cG
    cT
    @9
    @1
    cdif
    #
    cres
    #
    cdprd
    co
    #
    chash
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    wi
    #
    wi
    wph
    c0
    cA
    wss
    #
    cP
    cG
    c0
    cdprd
    co
    #
    chash
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    wi
    #
    wi
    wph
    vz
    cv
    #
    cA
    wss
    #
    cP
    cG
    cT
    @24
    @1
    cdif
    #
    cres
    #
    cdprd
    co
    #
    chash
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    wi
    #
    wi
    wph
    @24
    vq
    cv
    #
    csn
    #
    cun
    #
    cA
    wss
    #
    cP
    cG
    cT
    @35
    @1
    cdif
    #
    cres
    #
    cdprd
    co
    #
    chash
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    wi
    #
    wi
    wph
    @8
    wi
    vy
    vz
    vq
    cA
    @9
    c0
    wceq
    #
    @17
    @23
    wph
    @44
    @10
    @18
    @16
    @22
    @9
    c0
    cA
    sseq1
    @44
    @15
    @21
    @44
    @14
    @20
    cP
    cdvds
    @44
    @13
    @19
    chash
    @44
    @12
    c0
    cG
    cdprd
    @44
    @12
    cT
    c0
    cres
    #
    c0
    @44
    @11
    c0
    cT
    @44
    @11
    c0
    @1
    cdif
    #
    c0
    @9
    c0
    @1
    difeq1
    @1
    0dif
    #
    syl6eq
    reseq2d
    cT
    res0
    #
    syl6eq
    oveq2d
    fveq2d
    breq2d
    notbid
    imbi12d
    imbi2d
    @9
    @24
    wceq
    #
    @17
    @32
    wph
    @49
    @10
    @25
    @16
    @31
    @9
    @24
    cA
    sseq1
    @49
    @15
    @30
    @49
    @14
    @29
    cP
    cdvds
    @49
    @13
    @28
    chash
    @49
    @12
    @27
    cG
    cdprd
    @49
    @11
    @26
    cT
    @9
    @24
    @1
    difeq1
    reseq2d
    oveq2d
    fveq2d
    breq2d
    notbid
    imbi12d
    imbi2d
    @9
    @35
    wceq
    #
    @17
    @43
    wph
    @50
    @10
    @36
    @16
    @42
    @9
    @35
    cA
    sseq1
    @50
    @15
    @41
    @50
    @14
    @40
    cP
    cdvds
    @50
    @13
    @39
    chash
    @50
    @12
    @38
    cG
    cdprd
    @50
    @11
    @37
    cT
    @9
    @35
    @1
    difeq1
    reseq2d
    oveq2d
    fveq2d
    breq2d
    notbid
    imbi12d
    imbi2d
    @9
    cA
    wceq
    #
    @17
    @8
    wph
    @51
    @10
    @0
    @16
    @7
    @9
    cA
    cA
    sseq1
    @51
    @15
    @6
    @51
    @14
    @5
    cP
    cdvds
    @51
    @13
    @4
    chash
    @51
    @12
    @3
    cG
    cdprd
    @51
    @11
    @2
    cT
    @9
    cA
    @1
    difeq1
    reseq2d
    oveq2d
    fveq2d
    breq2d
    notbid
    imbi12d
    imbi2d
    wph
    @22
    @18
    wph
    @21
    cP
    c1
    cdvds
    wbr
    #
    wph
    cP
    cprime
    wcel
    #
    @52
    wn
    #
    ablfac1eulem.1
    cP
    nprmdvds1
    syl
    #
    wph
    @20
    c1
    cP
    cdvds
    wph
    @20
    cG
    c0g
    cfv
    #
    csn
    #
    chash
    cfv
    #
    c1
    wph
    @19
    @57
    chash
    wph
    cG
    c0
    cdprd
    cdm
    #
    wbr
    #
    @19
    @57
    wceq
    #
    wph
    cG
    cabl
    wcel
    cG
    cgrp
    wcel
    @60
    @61
    wa
    ablfac1.g
    cG
    ablgrp
    cG
    @56
    @56
    eqid
    #
    dprd0
    3syl
    simprd
    #
    fveq2d
    @56
    cvv
    wcel
    @58
    c1
    wceq
    cG
    c0g
    fvex
    @56
    cvv
    hashsng
    ax-mp
    #
    syl6eq
    breq2d
    mtbird
    a1d
    @24
    cfn
    wcel
    #
    @33
    @24
    wcel
    wn
    #
    wa
    wph
    @32
    @43
    @66
    wph
    @32
    @43
    wi
    #
    wi
    @65
    wph
    @66
    @67
    @32
    @36
    @31
    wi
    wph
    @66
    wa
    #
    @43
    @36
    @25
    @31
    @24
    @35
    wss
    #
    @36
    @25
    @24
    @34
    ssun1
    #
    @24
    @35
    cA
    sstr
    mpan
    imim1i
    @68
    @36
    @31
    @42
    wph
    @66
    @36
    @31
    @42
    wi
    wph
    @66
    @36
    wa
    #
    wa
    #
    @41
    @30
    @72
    @41
    @30
    cP
    cG
    cT
    @34
    @1
    cdif
    #
    cres
    #
    cdprd
    co
    #
    chash
    cfv
    #
    cdvds
    wbr
    #
    wo
    #
    @30
    @72
    @41
    cP
    @29
    @76
    cmul
    co
    #
    cdvds
    wbr
    #
    @78
    @72
    @40
    @79
    cP
    cdvds
    @72
    @40
    cG
    @38
    @26
    cres
    #
    cdprd
    co
    #
    cG
    @38
    @73
    cres
    #
    cdprd
    co
    #
    cG
    clsm
    cfv
    #
    co
    #
    chash
    cfv
    @82
    chash
    cfv
    #
    @84
    chash
    cfv
    #
    cmul
    co
    @79
    @72
    @39
    @86
    chash
    @72
    @26
    @73
    @85
    @38
    cG
    @37
    @72
    cA
    cG
    csubg
    cfv
    #
    @37
    cT
    wph
    cA
    @89
    cT
    wf
    @71
    wph
    cT
    cG
    cA
    wph
    cG
    cT
    @59
    wbr
    #
    cG
    cT
    cdprd
    co
    #
    cB
    wceq
    ablfac1eu.1
    simpld
    #
    ablfac1eu.2
    dprdf2
    adantr
    @72
    @35
    cA
    @1
    wph
    @66
    @36
    simprr
    #
    ssdifssd
    #
    fssresd
    #
    @72
    @24
    @34
    cin
    #
    @1
    cdif
    @46
    @26
    @73
    cin
    c0
    @72
    @96
    c0
    @1
    @72
    @66
    @96
    c0
    wceq
    wph
    @66
    @36
    simprl
    @24
    @33
    disjsn
    sylibr
    difeq1d
    @24
    @34
    @1
    difindir
    @47
    3eqtr3g
    #
    @37
    @26
    @73
    cun
    wceq
    @72
    @24
    @34
    @1
    difundir
    a1i
    @85
    eqid
    #
    @72
    cG
    @38
    @59
    wbr
    @39
    @91
    wss
    @72
    @37
    cT
    cG
    cA
    wph
    @90
    @71
    @92
    adantr
    wph
    cT
    cdm
    cA
    wceq
    #
    @71
    ablfac1eu.2
    adantr
    @94
    dprdres
    simpld
    #
    dprdsplit
    fveq2d
    @72
    @85
    @82
    @84
    cG
    @56
    cG
    ccntz
    cfv
    #
    @98
    @62
    @101
    eqid
    #
    @72
    cG
    @81
    @59
    wbr
    #
    @82
    @89
    wcel
    @72
    @103
    @82
    @39
    wss
    @72
    @26
    @38
    cG
    @37
    @100
    @72
    @37
    @89
    @38
    wf
    @38
    cdm
    @37
    wceq
    @95
    @37
    @89
    @38
    fdm
    syl
    #
    @69
    @26
    @37
    wss
    @72
    @70
    @24
    @35
    @1
    ssdif
    mp1i
    #
    dprdres
    simpld
    @81
    cG
    dprdsubg
    syl
    @72
    cG
    @83
    @59
    wbr
    #
    @84
    @89
    wcel
    @72
    @106
    @84
    @39
    wss
    @72
    @73
    @38
    cG
    @37
    @100
    @104
    @34
    @35
    wss
    @73
    @37
    wss
    @72
    @34
    @24
    ssun2
    @34
    @35
    @1
    ssdif
    mp1i
    #
    dprdres
    simpld
    @83
    cG
    dprdsubg
    syl
    @72
    @26
    @73
    @38
    cG
    @37
    @56
    @100
    @104
    @105
    @107
    @97
    @62
    dprddisj2
    @72
    @26
    @73
    @38
    cG
    @37
    @101
    @100
    @104
    @105
    @107
    @97
    @102
    dprdcntz2
    @72
    cB
    cfn
    wcel
    #
    @82
    cB
    wss
    @82
    cfn
    wcel
    wph
    @108
    @71
    ablfac1.f
    adantr
    #
    cB
    @81
    cG
    ablfac1.b
    dprdssv
    cB
    @82
    ssfi
    sylancl
    @72
    @108
    @84
    cB
    wss
    @84
    cfn
    wcel
    @109
    cB
    @83
    cG
    ablfac1.b
    dprdssv
    cB
    @84
    ssfi
    sylancl
    lsmhash
    @72
    @87
    @29
    @88
    @76
    cmul
    @72
    @82
    @28
    chash
    @72
    @81
    @27
    cG
    cdprd
    @72
    cT
    @26
    @37
    @105
    resabs1d
    oveq2d
    fveq2d
    @72
    @84
    @75
    chash
    @72
    @83
    @74
    cG
    cdprd
    @72
    cT
    @73
    @37
    @107
    resabs1d
    oveq2d
    fveq2d
    oveq12d
    3eqtrd
    breq2d
    @72
    @53
    @29
    cz
    wcel
    @76
    cz
    wcel
    @80
    @78
    wb
    wph
    @53
    @71
    ablfac1eulem.1
    adantr
    #
    @72
    @29
    @72
    @28
    cfn
    wcel
    #
    @29
    cn0
    wcel
    @72
    @108
    @28
    cB
    wss
    @111
    @109
    cB
    @27
    cG
    ablfac1.b
    dprdssv
    cB
    @28
    ssfi
    sylancl
    @28
    hashcl
    syl
    nn0zd
    @72
    @76
    @72
    @75
    cfn
    wcel
    #
    @76
    cn0
    wcel
    @72
    @108
    @75
    cB
    wss
    @112
    @109
    cB
    @74
    cG
    ablfac1.b
    dprdssv
    cB
    @75
    ssfi
    sylancl
    @75
    hashcl
    syl
    nn0zd
    cP
    @29
    @76
    euclemma
    syl3anc
    bitrd
    @72
    @77
    wn
    #
    @78
    @30
    wi
    @72
    @113
    @33
    cP
    @72
    @33
    cP
    wceq
    #
    wa
    #
    @77
    @52
    wph
    @54
    @71
    @114
    @55
    ad2antrr
    @115
    @76
    c1
    cP
    cdvds
    @115
    @76
    @58
    c1
    @115
    @75
    @57
    chash
    @115
    @75
    @19
    @57
    @115
    @74
    c0
    cG
    cdprd
    @115
    @74
    @45
    c0
    @115
    @73
    c0
    cT
    @115
    @73
    @1
    @1
    cdif
    c0
    @115
    @34
    @1
    @1
    @115
    @33
    cP
    @72
    @114
    simpr
    sneqd
    difeq1d
    @1
    difid
    syl6eq
    reseq2d
    @48
    syl6eq
    oveq2d
    wph
    @61
    @71
    @114
    @63
    ad2antrr
    eqtrd
    fveq2d
    @64
    syl6eq
    breq2d
    mtbird
    @72
    @33
    cP
    wne
    #
    wa
    #
    @77
    cP
    @33
    cC
    cexp
    co
    #
    cdvds
    wbr
    #
    @72
    @116
    @119
    wn
    @72
    @119
    @33
    cP
    @72
    @119
    cP
    @33
    wceq
    #
    @114
    @72
    @53
    @33
    cprime
    wcel
    cC
    cn0
    wcel
    #
    @119
    @120
    wi
    @110
    @72
    cA
    cprime
    @33
    wph
    cA
    cprime
    wss
    @71
    ablfac1.1
    adantr
    @72
    @34
    cA
    wss
    @33
    cA
    wcel
    #
    @72
    @24
    @34
    cA
    @93
    unssbd
    @33
    cA
    vq
    vex
    snss
    sylibr
    #
    sseldd
    wph
    @71
    @122
    @121
    @123
    ablfac1eu.3
    syldan
    cP
    @33
    cC
    prmdvdsexpr
    syl3anc
    cP
    @33
    eqcom
    syl6ib
    necon3ad
    imp
    @117
    @76
    @118
    cP
    cdvds
    @117
    @76
    @33
    cT
    cfv
    #
    chash
    cfv
    #
    @118
    @117
    @75
    @124
    chash
    @117
    cG
    cT
    @34
    cres
    #
    cdprd
    co
    @75
    @124
    @117
    @126
    @74
    cG
    cdprd
    @117
    @34
    @73
    cT
    @117
    @34
    @1
    cin
    c0
    wceq
    #
    @34
    @73
    wceq
    @116
    @127
    @72
    @33
    cP
    disjsn2
    adantl
    @34
    @1
    disj3
    sylib
    reseq2d
    oveq2d
    @117
    cT
    cG
    cA
    @33
    wph
    @90
    @71
    @116
    @92
    ad2antrr
    wph
    @99
    @71
    @116
    ablfac1eu.2
    ad2antrr
    @72
    @122
    @116
    @123
    adantr
    dpjlem
    eqtr3d
    fveq2d
    @72
    @125
    @118
    wceq
    #
    @116
    wph
    @71
    @122
    @128
    @123
    ablfac1eu.4
    syldan
    adantr
    eqtrd
    breq2d
    mtbird
    pm2.61dane
    @77
    @30
    orel2
    syl
    sylbid
    con3d
    expr
    a2d
    syl5
    expcom
    adantl
    a2d
    findcard2s
    mpcom
    mpi
end
